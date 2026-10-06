import psycopg2
import argparse
import re
from pglast import parse_plpgsql, parse_sql
from pglast.visitors import Visitor

parser = argparse.ArgumentParser(description="Рекурсивный анализ зависимостей PostgreSQL")
parser.add_argument("--host", default="pgsql-dev.taximaxim.local")
parser.add_argument("--port", type=int, default=5432)
parser.add_argument("--db", default="query_dev")
parser.add_argument("--user", default=None)
parser.add_argument("--proc-schema", default="smz")
parser.add_argument("--proc-name", default="smz_document_registration_job")
args = parser.parse_args()

conn = psycopg2.connect(
    host=args.host, port=args.port, dbname=args.db, user=args.user, connect_timeout=5
)
conn.autocommit = True
cur = conn.cursor()

BUILTIN_FUNCTIONS = {
    'format', 'coalesce', 'nullif', 'greatest', 'least',
    'count', 'sum', 'avg', 'min', 'max', 'array_agg', 'string_agg',
    'now', 'current_timestamp', 'current_date', 'current_time',
    'lower', 'upper', 'trim', 'length', 'substring', 'replace',
    'bool_or', 'bool_and', 'every', 'json_agg', 'jsonb_agg'
}

SYSTEM_SCHEMAS = ('pg_catalog', 'information_schema', 'pg_toast')

def resolve_object(dep_schema, dep_name):
    """Определяет тип объекта и его реальную схему."""
    if dep_schema:
        cur.execute("""
            SELECT relkind, n.nspname FROM pg_class c
            JOIN pg_namespace n ON c.relnamespace = n.oid
            WHERE n.nspname = %s AND c.relname = %s
        """, (dep_schema, dep_name))
        res = cur.fetchone()
        if res:
            kind, actual_schema = res
            if kind in ('r', 'p'): return ('table', actual_schema)
            if kind in ('v', 'm'): return ('view', actual_schema)
        
        cur.execute("""
            SELECT n.nspname FROM pg_proc p
            JOIN pg_namespace n ON p.pronamespace = n.oid
            WHERE n.nspname = %s AND p.proname = %s
        """, (dep_schema, dep_name))
        if cur.fetchone():
            return ('function', dep_schema)
        return ('unknown', dep_schema)

    cur.execute("""
        SELECT relkind, n.nspname FROM pg_class c
        JOIN pg_namespace n ON c.relnamespace = n.oid
        WHERE c.relname = %s AND n.nspname NOT IN %s
        ORDER BY n.nspname LIMIT 1
    """, (dep_name, SYSTEM_SCHEMAS))
    res = cur.fetchone()
    if res:
        kind, actual_schema = res
        if kind in ('r', 'p'): return ('table', actual_schema)
        if kind in ('v', 'm'): return ('view', actual_schema)

    cur.execute("""
        SELECT n.nspname FROM pg_proc p
        JOIN pg_namespace n ON p.pronamespace = n.oid
        WHERE p.proname = %s AND n.nspname NOT IN %s
        ORDER BY n.nspname LIMIT 1
    """, (dep_name, SYSTEM_SCHEMAS))
    res = cur.fetchone()
    if res:
        return ('function', res[0])

    return ('unknown', 'public')

def get_view_base_tables(view_schema: str, view_name: str) -> set:
    """Рекурсивно находит все базовые таблицы, от которых зависит вьюха."""
    base_tables = set()
    try:
        cur.execute("""
            WITH RECURSIVE view_deps AS (
                SELECT c.oid
                FROM pg_class c
                JOIN pg_namespace n ON c.relnamespace = n.oid
                WHERE n.nspname = %s AND c.relname = %s AND c.relkind IN ('v', 'm')
                
                UNION ALL
                
                SELECT c.oid
                FROM pg_depend d
                JOIN view_deps vd ON d.objid = vd.oid
                JOIN pg_class c ON d.refobjid = c.oid
                WHERE d.deptype IN ('n', 'a')
                  AND c.relkind IN ('r', 'p', 'v', 'm')
            )
            SELECT DISTINCT n.nspname, c.relname
            FROM view_deps vd
            JOIN pg_class c ON vd.oid = c.oid
            JOIN pg_namespace n ON c.relnamespace = n.oid
            WHERE c.relkind IN ('r', 'p')
              AND n.nspname NOT IN ('pg_catalog', 'information_schema', 'pg_toast')
        """, (view_schema, view_name))
        
        for row in cur.fetchall():
            base_tables.add((row[0], row[1]))
    except psycopg2.Error as e:
        print(f"   ⚠ Ошибка при раскрытии вьюхи {view_schema}.{view_name}: {e}")
        
    return base_tables

class DependencyVisitor(Visitor):
    def __init__(self):
        super().__init__()
        self.objects = set()
    
    def visit_RangeVar(self, ancestors, node):
        schema = node.schemaname
        if schema not in SYSTEM_SCHEMAS:
            self.objects.add((schema, node.relname))
    
    def visit_FuncCall(self, ancestors, node):
        names = [n.sval for n in node.funcname]
        if len(names) == 1:
            self.objects.add((None, names[0]))
        elif len(names) == 2:
            self.objects.add((names[0], names[1]))

def find_tables_in_strings(sql: str) -> set:
    found = set()
    pattern = r'(?:INSERT\s+INTO|FROM|UPDATE|JOIN)\s+([a-zA-Z_][a-zA-Z0-9_]*)\.([a-zA-Z_][a-zA-Z0-9_]*)'
    for match in re.finditer(pattern, sql, re.IGNORECASE):
        schema = match.group(1)
        table = match.group(2)
        if schema not in SYSTEM_SCHEMAS:
            found.add((schema, table))
    return found

def analyze_function(schema: str, name: str, visited: set, queue: list, final_tables: set):
    full_name = f"{schema}.{name}"
    if full_name in visited:
        return
    visited.add(full_name)
    
    try:
        cur.execute("""
            SELECT pg_get_functiondef(p.oid), l.lanname, p.prosrc
            FROM pg_proc p
            JOIN pg_namespace n ON p.pronamespace = n.oid
            JOIN pg_language l ON p.prolang = l.oid
            WHERE n.nspname = %s AND p.proname = %s AND p.prokind != 'a'
        """, (schema, name))
        res = cur.fetchone()
    except psycopg2.Error:
        return
        
    if not res:
        return
        
    func_def, lang, prosrc = res
    found_deps = set()
    
    found_deps.update(find_tables_in_strings(prosrc))
    
    if lang == 'plpgsql':
        try:
            plpgsql_ast = parse_plpgsql(func_def)
            def collect_sql(node):
                if isinstance(node, dict):
                    if 'PLpgSQL_expr' in node:
                        yield node['PLpgSQL_expr'].get('query', '')
                    for v in node.values():
                        yield from collect_sql(v)
                elif isinstance(node, (list, tuple)):
                    for item in node:
                        yield from collect_sql(item)

            sql_queries = [q for q in collect_sql(plpgsql_ast) if q.strip()]
            for sql in sql_queries:
                cleaned = sql.strip()
                if cleaned.upper().startswith('SELECT') and cleaned.rstrip().endswith(')'):
                    if cleaned.count(')') > cleaned.count('('):
                        cleaned = cleaned.rstrip()[:-1].strip()
                
                upper = cleaned.upper()
                if not any(upper.startswith(kw) for kw in ('SELECT', 'INSERT', 'UPDATE', 'DELETE', 'CALL', 'WITH')):
                    if '(' in cleaned and '.' in cleaned:
                        cleaned = f"SELECT {cleaned}"
                    else:
                        continue
                
                try:
                    ast = parse_sql(cleaned)
                    visitor = DependencyVisitor()
                    visitor(ast)
                    found_deps.update(visitor.objects)
                except Exception:
                    pass
        except Exception:
            pass
            
    elif lang == 'sql':
        try:
            ast = parse_sql(prosrc)
            visitor = DependencyVisitor()
            visitor(ast)
            found_deps.update(visitor.objects)
        except Exception:
            pass

    for dep_schema, dep_name in found_deps:
        if not dep_name or dep_name.lower() in BUILTIN_FUNCTIONS:
            continue
            
        obj_type, actual_schema = resolve_object(dep_schema, dep_name)
        
        if obj_type == 'table':
            final_tables.add((actual_schema, dep_name))
        elif obj_type == 'view':
            # Раскрываем вьюху до базовых таблиц
            base_tables = get_view_base_tables(actual_schema, dep_name)
            final_tables.update(base_tables)
        elif obj_type == 'function':
            if actual_schema in SYSTEM_SCHEMAS:
                continue
            if f"{actual_schema}.{dep_name}" not in visited:
                queue.append((actual_schema, dep_name))

# === ГЛАВНЫЙ ЦИКЛ ===
print("=" * 70)
print(f"НАЧАЛО АНАЛИЗА: {args.proc_schema}.{args.proc_name}")
print("=" * 70)

visited = set()
queue = [(args.proc_schema, args.proc_name)]
final_tables = set()

while queue:
    current_schema, current_name = queue.pop(0)
    analyze_function(current_schema, current_name, visited, queue, final_tables)

# === ИТОГИ ===
print("\n" + "=" * 70)
print("ИТОГОВЫЙ СПИСОК ЗАВИСИМОСТЕЙ")
print("=" * 70)

print(f"\n ТАБЛИЦЫ ({len(final_tables)}):")
for schema, name in sorted(final_tables):
    print(f"   {schema}.{name}")


cur.close()
conn.close()