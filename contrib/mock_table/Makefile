MODULE_big = mock_table
OBJS = mock_table.o deparse.o memo.o comms.o
EXTENSION = mock_table
DATA = mock_table--1.0.sql

PG_CONFIG = pg_config
PG_CPPFLAGS = -g -O0 -I$(libpq_srcdir)
SHLIB_LINK_INTERNAL = $(libpq)
SHLIB_LINK += -lcurl
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)