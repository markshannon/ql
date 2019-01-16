/** Provides class and predicates to track external data that
 * may represent malicious SQL queries or parts of queries.
 *
 * This module is intended to be imported into a taint-tracking query
 * to extend `TaintKind` and `TaintSink`.
 *
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Untrusted


/** A taint kind representing a DB cursor.
 * This will be overridden to provide specific kinds of DB cursor.
 */
abstract class DbCursor extends TaintKind {

    bindingset[this]
    DbCursor() { any() }

    string getExecuteMethodName() { result = "execute" }

}

/** A taint source representing sources of DB connections.
 * This will be overridden to provide specific kinds of DB connection sources.
 */
abstract class DbConnectionSource extends TaintSource {

}

/** A taint sink that is vulnerable to malicious SQL queries.
 * The `vuln` in `db.connection.execute(vuln)` and similar.
 */
class DbConnectionExecuteArgument extends TaintSink {

    override string toString() { result = "db.connection.execute" }

    DbConnectionExecuteArgument() {
        exists(CallNode call, DbCursor cursor, string name |
            cursor.taints(call.getFunction().(AttrNode).getObject(name)) and
            cursor.getExecuteMethodName() = name and
            call.getArg(0) = this
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }
}


