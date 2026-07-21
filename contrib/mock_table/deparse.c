#include "postgres.h"

#include "access/htup_details.h"
#include "access/table.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/ruleutils.h"
#include "utils/syscache.h"

#include "mock_table.h"

#define MOCK_REL_ALIAS_PREFIX "r"

static const char *mock_deparse_dest_source = NULL;

static bool
mock_parse_source_prefix(const char *relname, char *source, int source_sz, const char **base_name)
{
	const char *sep;
	int		 len;

	if (relname == NULL || source == NULL || source_sz <= 1)
		return false;

	sep = strchr(relname, '_');
	if (sep == NULL || sep == relname)
		return false;

	if (strncmp(relname, "pg", 2) != 0)
		return false;

	len = (int) (sep - relname);
	if (len >= source_sz)
		return false;

	memcpy(source, relname, len);
	source[len] = '\0';
	if (base_name != NULL)
		*base_name = sep + 1;

	return true;
}

static RangeTblEntry *
mock_planner_rt_fetch(PlannerInfo *root, Index rti)
{
	RangeTblEntry *rte = NULL;

	if (root->simple_rte_array != NULL && rti < root->simple_rel_array_size)
		rte = root->simple_rte_array[rti];
	if (rte == NULL)
		rte = rt_fetch(rti, root->parse->rtable);

	return rte;
}

static void mock_deparse_expr(StringInfo buf, PlannerInfo *root, Node *node,
								  bool *supported);

typedef struct MockFlattenCtx
{
	List   *from_rels;
	List   *where_conds;
} MockFlattenCtx;



static void
mock_append_operator_name(StringInfo buf, Oid opno, bool *supported)
{
	HeapTuple	opertup;
	Form_pg_operator operform;

	opertup = SearchSysCache1(OPEROID, ObjectIdGetDatum(opno));
	if (!HeapTupleIsValid(opertup))
	{
		*supported = false;
		return;
	}

	operform = (Form_pg_operator) GETSTRUCT(opertup);
	if (operform->oprnamespace != PG_CATALOG_NAMESPACE)
	{
		const char *opnspname;

		opnspname = get_namespace_name(operform->oprnamespace);
		appendStringInfo(buf, "OPERATOR(%s.%s)",
						 quote_identifier(opnspname),
						 NameStr(operform->oprname));
	}
	else
		appendStringInfoString(buf, NameStr(operform->oprname));

	ReleaseSysCache(opertup);
}

static void
mock_deparse_relation_ref(StringInfo buf, PlannerInfo *root, RelOptInfo *rel,
						  bool *supported)
{
	RangeTblEntry *rte;
	Relation	table;
	const char *nspname;
	const char *relname;
	const char *remote_relname;
	const char *remote_nspname;
	char		source[64];

	if (!IS_SIMPLE_REL(rel))
	{
		*supported = false;
		appendStringInfoString(buf, "<unsupported-rel>");
		return;
	}

	rte = mock_planner_rt_fetch(root, rel->relid);
	if (rte == NULL || rte->rtekind != RTE_RELATION)
	{
		*supported = false;
		appendStringInfoString(buf, "<unsupported-rte>");
		return;
	}

	table = table_open(rte->relid, NoLock);
	nspname = mock_table_remote_schema_name();
	if (nspname == NULL || nspname[0] == '\0')
		nspname = get_namespace_name(RelationGetNamespace(table));
	relname = RelationGetRelationName(table);

	/*
	 * if source is local (public.pgN_table). For non-destination sources,
	 * remote.pgN_table.
	 */
	remote_relname = relname;
	remote_nspname = nspname;

	if (mock_parse_source_prefix(relname, source, sizeof(source), NULL))
	{
		if (mock_deparse_dest_source == NULL || strcmp(source, mock_deparse_dest_source) == 0)
		{
			/* Destination source is local on that target DB. */
			remote_relname = relname;
			remote_nspname = nspname;
		}
		else
		{
			/* Non-destination sources remain remote on target DB. */
			remote_relname = relname;
			remote_nspname = "remote";
		}
	}

	appendStringInfo(buf, "%s %s%d",
					 quote_qualified_identifier(remote_nspname, remote_relname),
					 MOCK_REL_ALIAS_PREFIX,
					 rel->relid);
	table_close(table, NoLock);
}

static void
mock_deparse_var(StringInfo buf, PlannerInfo *root, Var *var, bool *supported)
{
	RangeTblEntry *rte;
	char		   *attname;

	if (var->varlevelsup != 0 || IS_SPECIAL_VARNO(var->varno))
	{
		*supported = false;
		appendStringInfoString(buf, "<unsupported-var>");
		return;
	}

	rte = mock_planner_rt_fetch(root, var->varno);
	if (rte == NULL || rte->rtekind != RTE_RELATION)
	{
		*supported = false;
		appendStringInfoString(buf, "<unsupported-var>");
		return;
	}

	if (var->varattno == 0)
	{
		appendStringInfo(buf, "%s%d.*", MOCK_REL_ALIAS_PREFIX, var->varno);
		return;
	}

	if (var->varattno < 0)
	{
		*supported = false;
		appendStringInfoString(buf, "<unsupported-system-column>");
		return;
	}

	attname = get_attname(rte->relid, var->varattno, false);
	appendStringInfo(buf, "%s%d.%s",
					 MOCK_REL_ALIAS_PREFIX,
					 var->varno,
					 quote_identifier(attname));
}

static void
mock_deparse_const(StringInfo buf, Const *c)
{
	if (c->constisnull)
	{
		appendStringInfoString(buf, "NULL");
		return;
	}

	appendStringInfoString(buf, deparse_expression((Node *) c, NIL, false, false));
}

static void
mock_deparse_bool_expr(StringInfo buf, PlannerInfo *root, BoolExpr *expr,
					   bool *supported)
{
	const char *op = NULL;
	ListCell   *lc;
	bool		first = true;

	switch (expr->boolop)
	{
		case AND_EXPR:
			op = "AND";
			break;
		case OR_EXPR:
			op = "OR";
			break;
		case NOT_EXPR:
			appendStringInfoString(buf, "(NOT ");
			mock_deparse_expr(buf, root, linitial(expr->args), supported);
			appendStringInfoChar(buf, ')');
			return;
	}

	appendStringInfoChar(buf, '(');
	foreach(lc, expr->args)
	{
		if (!first)
			appendStringInfo(buf, " %s ", op);
		mock_deparse_expr(buf, root, lfirst(lc), supported);
		first = false;
	}
	appendStringInfoChar(buf, ')');
}



static void
mock_deparse_op_expr(StringInfo buf, PlannerInfo *root, OpExpr *expr,
					 bool *supported)
{
	appendStringInfoChar(buf, '(');

	if (list_length(expr->args) == 2)
	{
		mock_deparse_expr(buf, root, linitial(expr->args), supported);
		appendStringInfoChar(buf, ' ');
		mock_append_operator_name(buf, expr->opno, supported);
		appendStringInfoChar(buf, ' ');
		mock_deparse_expr(buf, root, lsecond(expr->args), supported);
	}
	else if (list_length(expr->args) == 1)
	{
		mock_append_operator_name(buf, expr->opno, supported);
		appendStringInfoChar(buf, ' ');
		mock_deparse_expr(buf, root, linitial(expr->args), supported);
	}
	else
		*supported = false;

	appendStringInfoChar(buf, ')');
}

static void
mock_deparse_null_test(StringInfo buf, PlannerInfo *root, NullTest *expr,
					   bool *supported)
{
	appendStringInfoChar(buf, '(');
	mock_deparse_expr(buf, root, (Node *) expr->arg, supported);
	if (expr->nulltesttype == IS_NULL)
		appendStringInfoString(buf, " IS NULL)");
	else
		appendStringInfoString(buf, " IS NOT NULL)");
}

static void
mock_deparse_expr(StringInfo buf, PlannerInfo *root, Node *node, bool *supported)
{
	if (!*supported)
		return;

	if (node == NULL)
	{
		appendStringInfoString(buf, "NULL");
		return;
	}

	switch (nodeTag(node))
	{
		case T_Var:
			mock_deparse_var(buf, root, (Var *) node, supported);
			break;
		case T_Const:
			mock_deparse_const(buf, (Const *) node);
			break;
		case T_OpExpr:
			mock_deparse_op_expr(buf, root, (OpExpr *) node, supported);
			break;
		case T_BoolExpr:
			mock_deparse_bool_expr(buf, root, (BoolExpr *) node, supported);
			break;
		case T_RelabelType:
			mock_deparse_expr(buf, root,
						  (Node *) ((RelabelType *) node)->arg,
						  supported);
			break;
		case T_NullTest:
			mock_deparse_null_test(buf, root, (NullTest *) node, supported);
			break;
		case T_FuncExpr:
			*supported = false;
			appendStringInfo(buf, "<unsupported-node:%d>", (int) nodeTag(node));
			break;
		default:
			*supported = false;
			appendStringInfo(buf, "<unsupported-node:%d>", (int) nodeTag(node));
			break;
	}
}

static void
mock_append_target_list(StringInfo buf, PlannerInfo *root, List *exprs,
						bool *supported)
{
	ListCell   *lc;
	bool		first = true;

	foreach(lc, exprs)
	{
		if (!first)
			appendStringInfoString(buf, ", ");
		mock_deparse_expr(buf, root, lfirst(lc), supported);
		first = false;
	}

	if (first)
		appendStringInfoString(buf, "*");
}

static void
mock_append_clause_list(StringInfo buf, PlannerInfo *root, List *clauses,
					 bool *supported)
{
	ListCell   *lc;
	bool		first = true;

	foreach(lc, clauses)
	{
		Node   *node = (Node *) lfirst(lc);

		if (IsA(node, RestrictInfo))
			node = (Node *) ((RestrictInfo *) node)->clause;

		if (!first)
			appendStringInfoString(buf, " AND ");
		appendStringInfoChar(buf, '(');
		mock_deparse_expr(buf, root, node, supported);
		appendStringInfoChar(buf, ')');
		first = false;
	}
}

static void
mock_append_unique_clause(List **clauses, RestrictInfo *rinfo)
{
	ListCell   *lc;

	if (rinfo == NULL)
		return;

	foreach(lc, *clauses)
	{
		RestrictInfo *existing = lfirst_node(RestrictInfo, lc);

		if (existing == rinfo)
			return;
	}

	*clauses = lappend(*clauses, rinfo);
}

static void
mock_append_unique_clause_list(List **dst, List *src)
{
	ListCell   *lc;

	foreach(lc, src)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

		mock_append_unique_clause(dst, rinfo);
	}
}

static bool
mock_is_simple_equality_join_clause(RestrictInfo *rinfo)
{
	Expr	   *clause;
	OpExpr	   *op;
	char	   *opname;

	if (rinfo == NULL || rinfo->clause == NULL)
		return false;

	clause = rinfo->clause;
	if (!IsA(clause, OpExpr))
		return false;

	op = (OpExpr *) clause;
	if (list_length(op->args) != 2)
		return false;

	opname = get_opname(op->opno);
	if (opname == NULL)
		return false;

	return (strcmp(opname, "=") == 0);
}

static bool
mock_validate_join_conds_are_eq(List *join_conds)
{
	ListCell   *lc;

	foreach(lc, join_conds)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

		if (!mock_is_simple_equality_join_clause(rinfo))
			return false;
	}

	return true;
}

static bool
mock_extract_joinpath_inputs(Path *path,
						 RelOptInfo **outerrel,
						 RelOptInfo **innerrel,
						 List **restrictlist)
{
	Path	   *outerpath;
	Path	   *innerpath;
	CustomPath *cp;

	if (path == NULL)
		return false;

	/*
	 * For remote EXPLAIN generation we only support joinrels represented
	 * by CustomPath nodes built by this extension.
	 */
	if (!IsA(path, CustomPath))
		return false;

	cp = (CustomPath *) path;
	if (list_length(cp->custom_paths) != 2)
		return false;

	outerpath = (Path *) linitial(cp->custom_paths);
	innerpath = (Path *) lsecond(cp->custom_paths);
	if (outerpath == NULL || innerpath == NULL)
		return false;

	*outerrel = outerpath->parent;
	*innerrel = innerpath->parent;
	*restrictlist = NIL;

	/*
	 * custom_private layout for join paths:
	 *   [0] Integer destination rti
	 *   [1] List of RestrictInfo join clauses (optional)
	 */
	if (cp->custom_private != NIL && list_length(cp->custom_private) >= 2)
	{
		Node *n = (Node *) lsecond(cp->custom_private);

		if (n != NULL && IsA(n, List))
			*restrictlist = (List *) n;
	}

	return (*outerrel != NULL && *innerrel != NULL);
}

static void
mock_collect_rel_tree(RelOptInfo *rel, MockFlattenCtx *ctx, bool *supported)
{
	
	if (!*supported || rel == NULL)
		return;

	if (IS_SIMPLE_REL(rel))
	{
		if (!list_member_ptr(ctx->from_rels, rel))
			ctx->from_rels = lappend(ctx->from_rels, rel);

		mock_append_unique_clause_list(&ctx->where_conds, rel->baserestrictinfo);
		return;
	}

	if (!IS_JOIN_REL(rel))
	{
		*supported = false;
		return;
	}

	RelOptInfo *outerrel;
	RelOptInfo *innerrel;
	List	   *join_conds;
	outerrel = NULL;
	innerrel = NULL;
	join_conds = NIL;

	if (!mock_extract_joinpath_inputs(rel->cheapest_total_path,
								 &outerrel,
								 &innerrel,
								 &join_conds))
	{
		*supported = false;
		return;
	}

	if (!mock_validate_join_conds_are_eq(join_conds))
	{
		*supported = false;
		return;
	}

	mock_collect_rel_tree(outerrel, ctx, supported);
	mock_collect_rel_tree(innerrel, ctx, supported);
	mock_append_unique_clause_list(&ctx->where_conds, join_conds);
}

char *
mock_deparse_join_sql_for_source(PlannerInfo *root,
						 RelOptInfo *joinrel,
						 RelOptInfo *outerrel,
						 RelOptInfo *innerrel,
						 JoinType jointype,
						 List *restrictlist,
						 const char *dest_source,
						 bool *supported)
{
	StringInfoData buf;
	MockFlattenCtx ctx;
	ListCell   *lc;
	bool		first = true;
	const char *prev_dest_source;

	*supported = true;
	initStringInfo(&buf);
	ctx.from_rels = NIL;
	ctx.where_conds = NIL;

	prev_dest_source = mock_deparse_dest_source;
	mock_deparse_dest_source = dest_source;

	// only inner join supported
	if (jointype != JOIN_INNER)
	{
		*supported = false;
		elog(LOG, "mock_table deparse: unsupported non-inner join");
		mock_deparse_dest_source = prev_dest_source;
		return buf.data;
	}

	mock_collect_rel_tree(outerrel, &ctx, supported);
	mock_collect_rel_tree(innerrel, &ctx, supported);
	mock_append_unique_clause_list(&ctx.where_conds, restrictlist);

	if (!*supported || ctx.from_rels == NIL)
	{
		*supported = false;
		elog(LOG, "mock_table deparse: unsupported join tree for remote explain");
		mock_deparse_dest_source = prev_dest_source;
		return buf.data;
	}

	appendStringInfoString(&buf, "SELECT ");
	mock_append_target_list(&buf, root, joinrel->reltarget->exprs, supported);

	appendStringInfoString(&buf, " FROM ");
	foreach(lc, ctx.from_rels)
	{
		RelOptInfo *rel = lfirst_node(RelOptInfo, lc);

		if (!first)
			appendStringInfoString(&buf, ", ");
		mock_deparse_relation_ref(&buf, root, rel, supported);
		first = false;
	}

	if (ctx.where_conds != NIL)
	{
		appendStringInfoString(&buf, " WHERE ");
		mock_append_clause_list(&buf, root, ctx.where_conds, supported);
	}

	if (*supported)
		elog(LOG, "mock_table deparse SQL: %s", buf.data);

	mock_deparse_dest_source = prev_dest_source;

	return buf.data;
}

char *
mock_deparse_base_sql_for_source(PlannerInfo *root,
					 RelOptInfo *rel,
					 PathTarget *target,
					 const char *dest_source,
					 bool *supported)
{
	StringInfoData buf;
	const char *prev_dest_source;
	List       *target_exprs;

	*supported = true;
	initStringInfo(&buf);

	prev_dest_source = mock_deparse_dest_source;
	mock_deparse_dest_source = dest_source;

	if (root == NULL || rel == NULL || !IS_SIMPLE_REL(rel))
	{
		*supported = false;
		mock_deparse_dest_source = prev_dest_source;
		return buf.data;
	}

	target_exprs = (target != NULL) ? target->exprs : rel->reltarget->exprs;

	appendStringInfoString(&buf, "SELECT ");
	mock_append_target_list(&buf, root, target_exprs, supported);

	if (!*supported)
	{
		/*
		 * Fallback to * projection if target expression deparse is not
		 * supported for this baserel.
		 */
		resetStringInfo(&buf);
		*supported = true;
		appendStringInfoString(&buf, "SELECT *");
	}

	appendStringInfoString(&buf, " FROM ");
	mock_deparse_relation_ref(&buf, root, rel, supported);

	if (*supported && rel->baserestrictinfo != NIL)
	{
		appendStringInfoString(&buf, " WHERE ");
		mock_append_clause_list(&buf, root, rel->baserestrictinfo, supported);
	}

	if (*supported)
		elog(LOG, "mock_table deparse base SQL: %s", buf.data);

	mock_deparse_dest_source = prev_dest_source;

	return buf.data;
}
