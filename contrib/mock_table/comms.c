#include "postgres.h"

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#include "libpq-fe.h"
#include "miscadmin.h"
#include "utils/guc.h"
#include "utils/memutils.h"

#include "mock_table.h"

static char *mock_remote_host = NULL;
static int mock_remote_port = 5432;
static char *mock_remote_dbname = NULL;
static char *mock_remote_user = NULL;
static char *mock_remote_schema = NULL;
static double mock_data_movement_factor = 0.01;

bool mock_remote_explain_sql_for_source(const char *source,
							   const char *sql,
							   Cost *startup_cost,
							   Cost *total_cost,
							   Cardinality *rows,
							   int *width);

static int
mock_remote_port_for_source(const char *source)
{
	const char *p;
	long		 n;
	char		 *endptr;

	if (source == NULL)
		return mock_remote_port;

	if (strncmp(source, "pg", 2) != 0)
		return mock_remote_port;

	p = source + 2;
	if (*p == '\0')
		return mock_remote_port;

	n = strtol(p, &endptr, 10);
	if (*endptr != '\0' || n <= 0)
		return mock_remote_port;

	if (n > 10000)
		return mock_remote_port;

	// map pg1 -> base_port, pg2 -> base_port+1, ... 
	return mock_remote_port + ((int) n - 1);
}

static bool
mock_extract_json_number_field(const char *json, const char *key, double *value)
{
	char   *needle;
	char   *pos;
	char   *colon;
	char   *endptr;
	double	 parsed;

	needle = psprintf("\"%s\"", key);
	pos = strstr(json, needle);
	pfree(needle);
	if (pos == NULL)
		return false;

	colon = strchr(pos, ':');
	if (colon == NULL)
		return false;

	colon++;
	while (*colon != '\0' && isspace((unsigned char) *colon))
		colon++;

	parsed = strtod(colon, &endptr);
	if (endptr == colon)
		return false;

	*value = parsed;
	return true;
}

void
mock_table_define_comms_gucs(void)
{
	DefineCustomStringVariable("mock_table.remote_host",
							   "Remote server hostname for federated EXPLAIN.",
							   NULL,
							   &mock_remote_host,
							   "localhost",
							   PGC_USERSET,
							   0,
							   NULL,
							   NULL,
							   NULL);

	DefineCustomIntVariable("mock_table.remote_port",
						"Remote server port for federated EXPLAIN.",
						NULL,
						&mock_remote_port,
						5432,
						1,
						65535,
						PGC_USERSET,
						0,
						NULL,
						NULL,
						NULL);

	DefineCustomStringVariable("mock_table.remote_dbname",
							   "Remote database name for federated EXPLAIN.",
							   NULL,
							   &mock_remote_dbname,
							   "tpch",
							   PGC_USERSET,
							   0,
							   NULL,
							   NULL,
							   NULL);

	DefineCustomStringVariable("mock_table.remote_user",
							   "Remote user for federated EXPLAIN (empty uses current role).",
							   NULL,
							   &mock_remote_user,
							   "",
							   PGC_USERSET,
							   0,
							   NULL,
							   NULL,
							   NULL);

	DefineCustomStringVariable("mock_table.remote_schema",
							   "Remote schema used when deparsing remote relation names.",
							   NULL,
							   &mock_remote_schema,
							   "public",
							   PGC_USERSET,
							   0,
							   NULL,
							   NULL,
							   NULL);

	DefineCustomRealVariable("mock_table.data_movement_factor",
						 "Additional remote movement cost factor multiplied by rows.",
						 NULL,
						 &mock_data_movement_factor,
						 0.0,
						 0.0,
						 1.0e12,
						 PGC_USERSET,
						 0,
						 NULL,
						 NULL,
						 NULL);

}

const char *
mock_table_remote_schema_name(void)
{
	return mock_remote_schema;
}

double
mock_table_data_movement_factor(void)
{
	return mock_data_movement_factor;
}

bool
mock_remote_explain_sql(const char *sql,
						Cost *startup_cost,
						Cost *total_cost,
						Cardinality *rows,
						int *width)
{
	return mock_remote_explain_sql_for_source(NULL,
									 sql,
									 startup_cost,
									 total_cost,
									 rows,
									 width);
}

bool
mock_remote_explain_sql_for_source(const char *source,
							   const char *sql,
							   Cost *startup_cost,
							   Cost *total_cost,
							   Cardinality *rows,
							   int *width)
{
	PGconn	  *conn = NULL;
	PGresult  *res = NULL;
	char	   *conninfo;
	char	   *remote_user;
	char	   *explain_sql;
	char	   *json;
	int		 target_port;
	const char *target_source;
	const char *target_host;
	const char *target_dbname;
	double		startup;
	double		total;
	double		plan_rows;
	double		plan_width;
	bool		has_rows;
	bool		has_width;
	bool		ok = false;

	if (sql == NULL || startup_cost == NULL || total_cost == NULL)
		return false;

	remote_user = (mock_remote_user != NULL && mock_remote_user[0] != '\0') ?
		mock_remote_user : GetUserNameFromId(GetUserId(), false);
	target_source = (source != NULL && source[0] != '\0') ? source : "default";
	target_host = (mock_remote_host != NULL && mock_remote_host[0] != '\0') ?
		mock_remote_host : "localhost";
	target_dbname = (mock_remote_dbname != NULL && mock_remote_dbname[0] != '\0') ?
		mock_remote_dbname : "tpch";
	target_port = mock_remote_port_for_source(source);

	conninfo = psprintf("host=%s port=%d dbname=%s user=%s",
					  target_host,
					  target_port,
					  target_dbname,
					  remote_user);

	conn = PQconnectdb(conninfo);
	if (PQstatus(conn) != CONNECTION_OK)
	{
		elog(LOG,
			 "mock_table remote connect failed (source=%s host=%s port=%d db=%s): %s",
			 target_source,
			 target_host,
			 target_port,
			 target_dbname,
			 PQerrorMessage(conn));
		PQfinish(conn);
		pfree(conninfo);
		return false;
	}

	explain_sql = psprintf("EXPLAIN (FORMAT JSON) %s", sql);
	elog(LOG,
		 "mock_table issuing remote EXPLAIN (source=%s host=%s port=%d db=%s): %s",
		 target_source,
		 target_host,
		 target_port,
		 target_dbname,
		 explain_sql);
	res = PQexec(conn, explain_sql);
	if (res == NULL)
	{
		elog(LOG,
			 "mock_table remote EXPLAIN failed (source=%s host=%s port=%d db=%s): empty libpq result",
			 target_source,
			 target_host,
			 target_port,
			 target_dbname);
		goto done;
	}

	if (PQresultStatus(res) != PGRES_TUPLES_OK || PQntuples(res) < 1 || PQnfields(res) < 1)
	{
		elog(LOG,
			 "mock_table remote EXPLAIN failed (source=%s host=%s port=%d db=%s): %s",
			 target_source,
			 target_host,
			 target_port,
			 target_dbname,
			 PQerrorMessage(conn));
		goto done;
	}

	json = PQgetvalue(res, 0, 0);
	if (!mock_extract_json_number_field(json, "Startup Cost", &startup) ||
		!mock_extract_json_number_field(json, "Total Cost", &total))
	{
		elog(LOG,
			 "mock_table remote EXPLAIN JSON parse failed (source=%s host=%s port=%d db=%s) for costs",
			 target_source,
			 target_host,
			 target_port,
			 target_dbname);
		goto done;
	}

	has_rows = mock_extract_json_number_field(json, "Plan Rows", &plan_rows);
	has_width = mock_extract_json_number_field(json, "Plan Width", &plan_width);

	*startup_cost = (Cost) startup;
	*total_cost = (Cost) total;
	if (has_rows && rows != NULL)
		*rows = (Cardinality) plan_rows;
	if (has_width && width != NULL)
		*width = (int) plan_width;

	ok = true;

done:
	if (res != NULL)
		PQclear(res);
	if (conn != NULL)
		PQfinish(conn);
	pfree(explain_sql);
	pfree(conninfo);
	return ok;
}
