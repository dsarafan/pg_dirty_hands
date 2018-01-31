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

    vacuum_set_xid_limits(rel, 0, 0, 0, 0,
                          &oldestXmin, &freezeLimit, &xidFullScanLimit,
                          &multiXactCutoff, &multiXactFullScanLimit);

    Buffer buf = ReadBuffer(rel, blkno);
    LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

    Page page = BufferGetPage(buf);
    ItemId itemid = PageGetItemId(page, offnum);
    HeapTupleHeader tuple = (HeapTupleHeader) PageGetItem(page, itemid);

    if (!force)
    {
        need_freeze = heap_prepare_freeze_tuple(tuple, freezeLimit, multiXactCutoff,
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

    vacuum_set_xid_limits(rel, 0, 0, 0, 0,
                          &oldestXmin, &freezeLimit, &xidFullScanLimit,
                          &multiXactCutoff, &multiXactFullScanLimit);

    Buffer buf = ReadBuffer(rel, blkno);
    LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

    Page page = BufferGetPage(buf);
    ItemId itemid = PageGetItemId(page, offnum);
    HeapTupleHeader tuple = (HeapTupleHeader) PageGetItem(page, itemid);

    result = heap_freeze_tuple(tuple, freezeLimit, multiXactCutoff);

    UnlockReleaseBuffer(buf);
    heap_close(rel, RowExclusiveLock);
    PG_RETURN_BOOL(result);
}
