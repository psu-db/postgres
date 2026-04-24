#ifndef MOCK_TABLE_H
#define MOCK_TABLE_H

#include "postgres.h"

#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/paths.h"

// for memo
typedef struct RemoteJoinCostEntry
{
	Relids		relids;
	Cost		startup_cost;
	Cost		total_cost;
	Cardinality rows;
	int			join_dest_rti;
	bool		valid;
} RemoteJoinCostEntry;

extern void mock_table_define_comms_gucs(void);

extern const char *mock_table_remote_schema_name(void);

extern double mock_table_data_movement_factor(void);

extern const char *mock_table_request_source_id(void);
extern const char *mock_table_local_source_id(void);

extern bool mock_remote_explain_sql(const char *sql,
							Cost *startup_cost,
							Cost *total_cost,
							Cardinality *rows,
							int *width);

extern bool mock_remote_explain_sql_for_source(const char *source,
								   const char *sql,
								   Cost *startup_cost,
								   Cost *total_cost,
								   Cardinality *rows,
								   int *width);

extern char *mock_deparse_base_sql(PlannerInfo *root,
							RelOptInfo *rel,
							bool *supported);

extern char *mock_deparse_base_sql_for_source(PlannerInfo *root,
								   RelOptInfo *rel,
								   const char *dest_source,
								   bool *supported);

extern char *mock_deparse_join_sql(PlannerInfo *root,
								 RelOptInfo *joinrel,
								 RelOptInfo *outerrel,
								 RelOptInfo *innerrel,
								 JoinType jointype,
								 List *restrictlist,
								 bool *supported);

extern char *mock_deparse_join_sql_for_source(PlannerInfo *root,
									RelOptInfo *joinrel,
									RelOptInfo *outerrel,
									RelOptInfo *innerrel,
									JoinType jointype,
									List *restrictlist,
									const char *dest_source,
									bool *supported);

#endif