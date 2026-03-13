#ifndef MOCK_TABLE_H
#define MOCK_TABLE_H

#include "postgres.h"

#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/paths.h"

typedef struct RemoteJoinCostEntry
{
	Relids		relids;
	Cost		startup_cost;
	Cost		total_cost;
	Cardinality rows;
	int			join_dest_rti;
	bool		valid;
} RemoteJoinCostEntry;

extern RemoteJoinCostEntry *get_plan_cost_from_remote(PlannerInfo *root,
												  RelOptInfo *joinrel);

extern char *mock_deparse_join_sql(PlannerInfo *root,
								 RelOptInfo *joinrel,
								 RelOptInfo *outerrel,
								 RelOptInfo *innerrel,
								 JoinType jointype,
								 List *restrictlist,
								 bool *supported);

#endif