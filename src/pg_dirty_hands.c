#include "postgres.h"
#include "miscadmin.h"
#include "catalog/index.h"
#include "commands/vacuum.h"
#include "storage/lmgr.h"
#include "storage/bufmgr.h"
#include "access/heapam_xlog.h"
#include "access/htup_details.h"

#define DatumGetItemPointer(X)   ((ItemPointer) DatumGetPointer(X))
#define PG_GETARG_ITEMPOINTER(n) DatumGetItemPointer(PG_GETARG_DATUM(n))

PG_MODULE_MAGIC;



#include "access/heapam.h"
#include "access/heapam_xlog.h"
#include "access/hio.h"
#include "access/multixact.h"
#include "access/parallel.h"
#include "access/relscan.h"
#include "access/sysattr.h"
#include "access/transam.h"
#include "access/tuptoaster.h"
#include "access/valid.h"
#include "access/visibilitymap.h"
#include "access/xact.h"
#include "access/xlog.h"
#include "access/xloginsert.h"
#include "access/xlogutils.h"
#include "catalog/catalog.h"
#include "catalog/namespace.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "storage/bufmgr.h"
#include "storage/freespace.h"
#include "storage/lmgr.h"
#include "storage/predicate.h"
#include "storage/procarray.h"
#include "storage/smgr.h"
#include "storage/spin.h"
#include "storage/standby.h"
#include "utils/datum.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"
#include "utils/relcache.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"
#include "utils/tqual.h"

#define		FRM_NOOP				0x0001
#define		FRM_INVALIDATE_XMAX		0x0002
#define		FRM_RETURN_IS_XID		0x0004
#define		FRM_RETURN_IS_MULTI		0x0008
#define		FRM_MARK_COMMITTED		0x0010


/* Get the LOCKMODE for a given MultiXactStatus */
#define LOCKMODE_from_mxstatus(status) \
			(tupleLockExtraInfo[TUPLOCK_from_mxstatus((status))].hwlock)

/*
 * Acquire heavyweight locks on tuples, using a LockTupleMode strength value.
 * This is more readable than having every caller translate it to lock.h's
 * LOCKMODE.
 */
#define LockTupleTuplock(rel, tup, mode) \
	LockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)
#define UnlockTupleTuplock(rel, tup, mode) \
	UnlockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)
#define ConditionalLockTupleTuplock(rel, tup, mode) \
	ConditionalLockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)

/*
 * This table maps tuple lock strength values for each particular
 * MultiXactStatus value.
 */
static const int MultiXactStatusLock[MaxMultiXactStatus + 1] =
{
	LockTupleKeyShare,			/* ForKeyShare */
	LockTupleShare,				/* ForShare */
	LockTupleNoKeyExclusive,	/* ForNoKeyUpdate */
	LockTupleExclusive,			/* ForUpdate */
	LockTupleNoKeyExclusive,	/* NoKeyUpdate */
	LockTupleExclusive			/* Update */
};

/* Get the LockTupleMode for a given MultiXactStatus */
#define TUPLOCK_from_mxstatus(status) \
			(MultiXactStatusLock[(status)])

static void
GetMultiXactIdHintBits(MultiXactId multi, uint16 *new_infomask,
					   uint16 *new_infomask2)
{
	int			nmembers;
	MultiXactMember *members;
	int			i;
	uint16		bits = HEAP_XMAX_IS_MULTI;
	uint16		bits2 = 0;
	bool		has_update = false;
	LockTupleMode strongest = LockTupleKeyShare;

	/*
	 * We only use this in multis we just created, so they cannot be values
	 * pre-pg_upgrade.
	 */
	nmembers = GetMultiXactIdMembers(multi, &members, false, false);

	for (i = 0; i < nmembers; i++)
	{
		LockTupleMode mode;

		/*
		 * Remember the strongest lock mode held by any member of the
		 * multixact.
		 */
		mode = TUPLOCK_from_mxstatus(members[i].status);
		if (mode > strongest)
			strongest = mode;

		/* See what other bits we need */
		switch (members[i].status)
		{
			case MultiXactStatusForKeyShare:
			case MultiXactStatusForShare:
			case MultiXactStatusForNoKeyUpdate:
				break;

			case MultiXactStatusForUpdate:
				bits2 |= HEAP_KEYS_UPDATED;
				break;

			case MultiXactStatusNoKeyUpdate:
				has_update = true;
				break;

			case MultiXactStatusUpdate:
				bits2 |= HEAP_KEYS_UPDATED;
				has_update = true;
				break;
		}
	}

	if (strongest == LockTupleExclusive ||
		strongest == LockTupleNoKeyExclusive)
		bits |= HEAP_XMAX_EXCL_LOCK;
	else if (strongest == LockTupleShare)
		bits |= HEAP_XMAX_SHR_LOCK;
	else if (strongest == LockTupleKeyShare)
		bits |= HEAP_XMAX_KEYSHR_LOCK;

	if (!has_update)
		bits |= HEAP_XMAX_LOCK_ONLY;

	if (nmembers > 0)
		pfree(members);

	*new_infomask = bits;
	*new_infomask2 = bits2;
}

static TransactionId
MultiXactIdGetUpdateXid(TransactionId xmax, uint16 t_infomask)
{
	TransactionId update_xact = InvalidTransactionId;
	MultiXactMember *members;
	int			nmembers;

	Assert(!(t_infomask & HEAP_XMAX_LOCK_ONLY));
	Assert(t_infomask & HEAP_XMAX_IS_MULTI);

	/*
	 * Since we know the LOCK_ONLY bit is not set, this cannot be a multi from
	 * pre-pg_upgrade.
	 */
	nmembers = GetMultiXactIdMembers(xmax, &members, false, false);

	if (nmembers > 0)
	{
		int			i;

		for (i = 0; i < nmembers; i++)
		{
			/* Ignore lockers */
			if (!ISUPDATE_from_mxstatus(members[i].status))
				continue;

			/* there can be at most one updater */
			Assert(update_xact == InvalidTransactionId);
			update_xact = members[i].xid;
#ifndef USE_ASSERT_CHECKING

			/*
			 * in an assert-enabled build, walk the whole array to ensure
			 * there's no other updater.
			 */
			break;
#endif
		}

		pfree(members);
	}

	return update_xact;
}

static TransactionId
FreezeMultiXactId_local(MultiXactId multi, uint16 t_infomask,
				  TransactionId cutoff_xid, MultiXactId cutoff_multi,
				  uint16 *flags)
{
	TransactionId xid = InvalidTransactionId;
	int			i;
	MultiXactMember *members;
	int			nmembers;
	bool		need_replace;
	int			nnewmembers;
	MultiXactMember *newmembers;
	bool		has_lockers;
	TransactionId update_xid;
	bool		update_committed;

	*flags = 0;

	/* We should only be called in Multis */
	Assert(t_infomask & HEAP_XMAX_IS_MULTI);

	if (!MultiXactIdIsValid(multi) ||
		HEAP_LOCKED_UPGRADED(t_infomask))
	{
		/* Ensure infomask bits are appropriately set/reset */
		*flags |= FRM_INVALIDATE_XMAX;
		return InvalidTransactionId;
	}
	else if (MultiXactIdPrecedes(multi, cutoff_multi))
	{
		/*
		 * This old multi cannot possibly have members still running.  If it
		 * was a locker only, it can be removed without any further
		 * consideration; but if it contained an update, we might need to
		 * preserve it.
		 */
		Assert(!MultiXactIdIsRunning(multi,
									 HEAP_XMAX_IS_LOCKED_ONLY(t_infomask)));
		if (HEAP_XMAX_IS_LOCKED_ONLY(t_infomask))
		{
			*flags |= FRM_INVALIDATE_XMAX;
			xid = InvalidTransactionId; /* not strictly necessary */
		}
		else
		{
			/* replace multi by update xid */
			xid = MultiXactIdGetUpdateXid(multi, t_infomask);

			/* wasn't only a lock, xid needs to be valid */
			Assert(TransactionIdIsValid(xid));

			/*
			 * If the xid is older than the cutoff, it has to have aborted,
			 * otherwise the tuple would have gotten pruned away.
			 */
			if (TransactionIdPrecedes(xid, cutoff_xid))
			{
				Assert(!TransactionIdDidCommit(xid));
				*flags |= FRM_INVALIDATE_XMAX;
				xid = InvalidTransactionId;		/* not strictly necessary */
			}
			else
			{
				*flags |= FRM_RETURN_IS_XID;
			}
		}

		return xid;
	}

	/*
	 * This multixact might have or might not have members still running, but
	 * we know it's valid and is newer than the cutoff point for multis.
	 * However, some member(s) of it may be below the cutoff for Xids, so we
	 * need to walk the whole members array to figure out what to do, if
	 * anything.
	 */

	nmembers =
		GetMultiXactIdMembers(multi, &members, false,
							  HEAP_XMAX_IS_LOCKED_ONLY(t_infomask));
	if (nmembers <= 0)
	{
		/* Nothing worth keeping */
		*flags |= FRM_INVALIDATE_XMAX;
		return InvalidTransactionId;
	}

	/* is there anything older than the cutoff? */
	need_replace = false;
	for (i = 0; i < nmembers; i++)
	{
		if (TransactionIdPrecedes(members[i].xid, cutoff_xid))
		{
			need_replace = true;
			break;
		}
	}

	/*
	 * In the simplest case, there is no member older than the cutoff; we can
	 * keep the existing MultiXactId as is.
	 */
	if (!need_replace)
	{
		*flags |= FRM_NOOP;
		pfree(members);
		return InvalidTransactionId;
	}

	/*
	 * If the multi needs to be updated, figure out which members do we need
	 * to keep.
	 */
	nnewmembers = 0;
	newmembers = palloc(sizeof(MultiXactMember) * nmembers);
	has_lockers = false;
	update_xid = InvalidTransactionId;
	update_committed = false;

	for (i = 0; i < nmembers; i++)
	{
		/*
		 * Determine whether to keep this member or ignore it.
		 */
		if (ISUPDATE_from_mxstatus(members[i].status))
		{
			TransactionId xid = members[i].xid;

			/*
			 * It's an update; should we keep it?  If the transaction is known
			 * aborted or crashed then it's okay to ignore it, otherwise not.
			 * Note that an updater older than cutoff_xid cannot possibly be
			 * committed, because HeapTupleSatisfiesVacuum would have returned
			 * HEAPTUPLE_DEAD and we would not be trying to freeze the tuple.
			 *
			 * As with all tuple visibility routines, it's critical to test
			 * TransactionIdIsInProgress before TransactionIdDidCommit,
			 * because of race conditions explained in detail in tqual.c.
			 */
			if (TransactionIdIsCurrentTransactionId(xid) ||
				TransactionIdIsInProgress(xid))
			{
				Assert(!TransactionIdIsValid(update_xid));
				update_xid = xid;
			}
			else if (TransactionIdDidCommit(xid))
			{
				/*
				 * The transaction committed, so we can tell caller to set
				 * HEAP_XMAX_COMMITTED.  (We can only do this because we know
				 * the transaction is not running.)
				 */
				Assert(!TransactionIdIsValid(update_xid));
				update_committed = true;
				update_xid = xid;
			}

			/*
			 * Not in progress, not committed -- must be aborted or crashed;
			 * we can ignore it.
			 */

			/*
			 * Since the tuple wasn't marked HEAPTUPLE_DEAD by vacuum, the
			 * update Xid cannot possibly be older than the xid cutoff.
			 */
			Assert(!TransactionIdIsValid(update_xid) ||
				   !TransactionIdPrecedes(update_xid, cutoff_xid));

			/*
			 * If we determined that it's an Xid corresponding to an update
			 * that must be retained, additionally add it to the list of
			 * members of the new Multi, in case we end up using that.  (We
			 * might still decide to use only an update Xid and not a multi,
			 * but it's easier to maintain the list as we walk the old members
			 * list.)
			 */
			if (TransactionIdIsValid(update_xid))
				newmembers[nnewmembers++] = members[i];
		}
		else
		{
			/* We only keep lockers if they are still running */
			if (TransactionIdIsCurrentTransactionId(members[i].xid) ||
				TransactionIdIsInProgress(members[i].xid))
			{
				/* running locker cannot possibly be older than the cutoff */
				Assert(!TransactionIdPrecedes(members[i].xid, cutoff_xid));
				newmembers[nnewmembers++] = members[i];
				has_lockers = true;
			}
		}
	}

	pfree(members);

	if (nnewmembers == 0)
	{
		/* nothing worth keeping!? Tell caller to remove the whole thing */
		*flags |= FRM_INVALIDATE_XMAX;
		xid = InvalidTransactionId;
	}
	else if (TransactionIdIsValid(update_xid) && !has_lockers)
	{
		/*
		 * If there's a single member and it's an update, pass it back alone
		 * without creating a new Multi.  (XXX we could do this when there's a
		 * single remaining locker, too, but that would complicate the API too
		 * much; moreover, the case with the single updater is more
		 * interesting, because those are longer-lived.)
		 */
		Assert(nnewmembers == 1);
		*flags |= FRM_RETURN_IS_XID;
		if (update_committed)
			*flags |= FRM_MARK_COMMITTED;
		xid = update_xid;
	}
	else
	{
		/*
		 * Create a new multixact with the surviving members of the previous
		 * one, to set as new Xmax in the tuple.
		 */
		xid = MultiXactIdCreateFromMembers(nnewmembers, newmembers);
		*flags |= FRM_RETURN_IS_MULTI;
	}

	pfree(newmembers);

	return xid;
}

static bool
heap_prepare_freeze_tuple_local(HeapTupleHeader tuple, TransactionId cutoff_xid,
						  TransactionId cutoff_multi,
						  xl_heap_freeze_tuple *frz, bool *totally_frozen_p)
{
	bool		changed = false;
	bool		freeze_xmax = false;
	TransactionId xid;
	bool		totally_frozen = true;

	frz->frzflags = 0;
	frz->t_infomask2 = tuple->t_infomask2;
	frz->t_infomask = tuple->t_infomask;
	frz->xmax = HeapTupleHeaderGetRawXmax(tuple);

	/* Process xmin */
	xid = HeapTupleHeaderGetXmin(tuple);
	if (TransactionIdIsNormal(xid))
	{
		if (TransactionIdPrecedes(xid, cutoff_xid))
		{
			frz->t_infomask |= HEAP_XMIN_FROZEN;
			changed = true;
		}
		else
			totally_frozen = false;
	}

	/*
	 * Process xmax.  To thoroughly examine the current Xmax value we need to
	 * resolve a MultiXactId to its member Xids, in case some of them are
	 * below the given cutoff for Xids.  In that case, those values might need
	 * freezing, too.  Also, if a multi needs freezing, we cannot simply take
	 * it out --- if there's a live updater Xid, it needs to be kept.
	 *
	 * Make sure to keep heap_tuple_needs_freeze in sync with this.
	 */
	xid = HeapTupleHeaderGetRawXmax(tuple);

	if (tuple->t_infomask & HEAP_XMAX_IS_MULTI)
	{
		TransactionId newxmax;
		uint16		flags;

		newxmax = FreezeMultiXactId_local(xid, tuple->t_infomask,
									cutoff_xid, cutoff_multi, &flags);

		if (flags & FRM_INVALIDATE_XMAX)
			freeze_xmax = true;
		else if (flags & FRM_RETURN_IS_XID)
		{
			/*
			 * NB -- some of these transformations are only valid because we
			 * know the return Xid is a tuple updater (i.e. not merely a
			 * locker.) Also note that the only reason we don't explicitly
			 * worry about HEAP_KEYS_UPDATED is because it lives in
			 * t_infomask2 rather than t_infomask.
			 */
			frz->t_infomask &= ~HEAP_XMAX_BITS;
			frz->xmax = newxmax;
			if (flags & FRM_MARK_COMMITTED)
				frz->t_infomask |= HEAP_XMAX_COMMITTED;
			changed = true;
			totally_frozen = false;
		}
		else if (flags & FRM_RETURN_IS_MULTI)
		{
			uint16		newbits;
			uint16		newbits2;

			/*
			 * We can't use GetMultiXactIdHintBits directly on the new multi
			 * here; that routine initializes the masks to all zeroes, which
			 * would lose other bits we need.  Doing it this way ensures all
			 * unrelated bits remain untouched.
			 */
			frz->t_infomask &= ~HEAP_XMAX_BITS;
			frz->t_infomask2 &= ~HEAP_KEYS_UPDATED;
			GetMultiXactIdHintBits(newxmax, &newbits, &newbits2);
			frz->t_infomask |= newbits;
			frz->t_infomask2 |= newbits2;

			frz->xmax = newxmax;

			changed = true;
			totally_frozen = false;
		}
		else
		{
			Assert(flags & FRM_NOOP);
		}
	}
	else if (TransactionIdIsNormal(xid))
	{
		if (TransactionIdPrecedes(xid, cutoff_xid))
			freeze_xmax = true;
		else
			totally_frozen = false;
	}

	if (freeze_xmax)
	{
		frz->xmax = InvalidTransactionId;

		/*
		 * The tuple might be marked either XMAX_INVALID or XMAX_COMMITTED +
		 * LOCKED.  Normalize to INVALID just to be sure no one gets confused.
		 * Also get rid of the HEAP_KEYS_UPDATED bit.
		 */
		frz->t_infomask &= ~HEAP_XMAX_BITS;
		frz->t_infomask |= HEAP_XMAX_INVALID;
		frz->t_infomask2 &= ~HEAP_HOT_UPDATED;
		frz->t_infomask2 &= ~HEAP_KEYS_UPDATED;
		changed = true;
	}

	/*
	 * Old-style VACUUM FULL is gone, but we have to keep this code as long as
	 * we support having MOVED_OFF/MOVED_IN tuples in the database.
	 */
	if (tuple->t_infomask & HEAP_MOVED)
	{
		xid = HeapTupleHeaderGetXvac(tuple);

		/*
		 * For Xvac, we ignore the cutoff_xid and just always perform the
		 * freeze operation.  The oldest release in which such a value can
		 * actually be set is PostgreSQL 8.4, because old-style VACUUM FULL
		 * was removed in PostgreSQL 9.0.  Note that if we were to respect
		 * cutoff_xid here, we'd need to make surely to clear totally_frozen
		 * when we skipped freezing on that basis.
		 */
		if (TransactionIdIsNormal(xid))
		{
			/*
			 * If a MOVED_OFF tuple is not dead, the xvac transaction must
			 * have failed; whereas a non-dead MOVED_IN tuple must mean the
			 * xvac transaction succeeded.
			 */
			if (tuple->t_infomask & HEAP_MOVED_OFF)
				frz->frzflags |= XLH_INVALID_XVAC;
			else
				frz->frzflags |= XLH_FREEZE_XVAC;

			/*
			 * Might as well fix the hint bits too; usually XMIN_COMMITTED
			 * will already be set here, but there's a small chance not.
			 */
			Assert(!(tuple->t_infomask & HEAP_XMIN_INVALID));
			frz->t_infomask |= HEAP_XMIN_COMMITTED;
			changed = true;
		}
	}

	*totally_frozen_p = totally_frozen;
	return changed;
}

PG_FUNCTION_INFO_V1(freeze_tuple);
Datum
freeze_tuple(PG_FUNCTION_ARGS)
{
    TransactionId oldestXmin,
                    freezeLimit,
                    xidFullScanLimit,
                    multiXactCutoff,
                    multiXactFullScanLimit;
    bool need_freeze, totally_frozen;
    xl_heap_freeze_tuple frz;

    Oid reloid = PG_GETARG_OID(0);
    ItemPointer tid = PG_GETARG_ITEMPOINTER(1);
    bool force = PG_GETARG_BOOL(2);

    BlockNumber blkno = ItemPointerGetBlockNumber(tid);
    OffsetNumber offnum = ItemPointerGetOffsetNumber(tid);

    Relation rel = heap_open(reloid, RowExclusiveLock);
    Buffer buf;
    Page page;
    ItemId itemid;
    HeapTupleHeader tuple;

    vacuum_set_xid_limits(rel, 0, 0, 0, 0,
                          &oldestXmin, &freezeLimit, &xidFullScanLimit,
                          &multiXactCutoff, &multiXactFullScanLimit);

    buf = ReadBuffer(rel, blkno);
    LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

    page = BufferGetPage(buf);
    itemid = PageGetItemId(page, offnum);
    tuple = (HeapTupleHeader) PageGetItem(page, itemid);

    if (!force)
    {
        need_freeze = heap_prepare_freeze_tuple_local(tuple, freezeLimit,  multiXactCutoff,
                                                    &frz, &totally_frozen);
    }
    else
    {
        need_freeze = true;

        /* Manually initialize freeze data */
        frz.frzflags = 0;
        frz.t_infomask2 = tuple->t_infomask2;
        frz.t_infomask = tuple->t_infomask;
        frz.xmax = HeapTupleHeaderGetRawXmax(tuple);

        /* Freeze xmin */
        frz.t_infomask |= HEAP_XMIN_FROZEN;

        /*
         * Freeze xmax.
         * The tuple might be marked either XMAX_INVALID or XMAX_COMMITTED +
         * LOCKED.  Normalize to INVALID just to be sure no one gets confused.
         * Also get rid of the HEAP_KEYS_UPDATED bit.
         */
        frz.t_infomask &= ~HEAP_XMAX_BITS;
        frz.t_infomask |= HEAP_XMAX_INVALID;
        frz.t_infomask2 &= ~HEAP_HOT_UPDATED;
        frz.t_infomask2 &= ~HEAP_KEYS_UPDATED;
        frz.xmax = InvalidTransactionId;
    }

    frz.offset = offnum;


    if (need_freeze)
    {
        START_CRIT_SECTION();

        MarkBufferDirty(buf);

        heap_execute_freeze_tuple(tuple, &frz);

        /* Now WAL-log freezing if necessary */
        if (RelationNeedsWAL(rel))
        {
            XLogRecPtr  recptr;

            recptr = log_heap_freeze(rel, buf, freezeLimit,
                                     &frz, 1);
            PageSetLSN(page, recptr);
        }

        END_CRIT_SECTION();
    }
    UnlockReleaseBuffer(buf);
    heap_close(rel, RowExclusiveLock);

    PG_RETURN_BOOL(need_freeze);
}

static bool
heap_freeze_tuple_local(HeapTupleHeader tuple, TransactionId cutoff_xid,
				  TransactionId cutoff_multi)
{
	xl_heap_freeze_tuple frz;
	bool		do_freeze;
	bool		tuple_totally_frozen;

	do_freeze = heap_prepare_freeze_tuple_local(tuple, cutoff_xid, cutoff_multi,
										  &frz, &tuple_totally_frozen);

	/*
	 * Note that because this is not a WAL-logged operation, we don't need to
	 * fill in the offset in the freeze record.
	 */

	if (do_freeze)
		heap_execute_freeze_tuple(tuple, &frz);
	return do_freeze;
}

PG_FUNCTION_INFO_V1(freeze_tuple_unlogged);
Datum
freeze_tuple_unlogged(PG_FUNCTION_ARGS)
{
    TransactionId oldestXmin,
                    freezeLimit,
                    xidFullScanLimit,
                    multiXactCutoff,
                    multiXactFullScanLimit;
    bool result;

    Oid reloid = PG_GETARG_OID(0);
    ItemPointer tid = PG_GETARG_ITEMPOINTER(1);

    BlockNumber blkno = ItemPointerGetBlockNumber(tid);
    OffsetNumber offnum = ItemPointerGetOffsetNumber(tid);

    Relation rel = heap_open(reloid, RowExclusiveLock);
    Buffer buf;
    Page page;
    ItemId itemid;
    HeapTupleHeader tuple;

    vacuum_set_xid_limits(rel, 0, 0, 0, 0,
                          &oldestXmin, &freezeLimit, &xidFullScanLimit,
                          &multiXactCutoff, &multiXactFullScanLimit);

    buf = ReadBuffer(rel, blkno);
    LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

    page = BufferGetPage(buf);
    itemid = PageGetItemId(page, offnum);
    tuple = (HeapTupleHeader) PageGetItem(page, itemid);

    result = heap_freeze_tuple_local(tuple, freezeLimit, multiXactCutoff);

    UnlockReleaseBuffer(buf);
    heap_close(rel, RowExclusiveLock);
    PG_RETURN_BOOL(result);
}
