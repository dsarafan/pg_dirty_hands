MODULE_big = pg_dirty_hands
OBJS = src/pg_dirty_hands.o $(WIN32RES)

EXTENSION = pg_dirty_hands
DATA = pg_dirty_hands--1.0.sql
PGFILEDESC = "Dirty hands extension"

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/pg_dirty_hands
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif
