#ifndef FQP_TRACE_H
#define FQP_TRACE_H

#include "postgres.h"

extern bool fqp_trace_is_active(void);
extern void fqp_trace_begin(const char *query_string);
extern void fqp_trace_finish(bool ok);

#endif
