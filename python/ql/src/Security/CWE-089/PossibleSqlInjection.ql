/**
 * @name SQL query built from concatenation of dynamic values.
 * @description Building a SQL query by concatenating dynamic and constant values is often vulnerable to insertion of
 *              malicious code by the user.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id py/sql-query-from-concatenation
 * @tags security
 *       external/cwe/cwe-089
 *       external/owasp/owasp-a1
 */

import python
import semmle.python.security.Paths


/* Sources */
import semmle.python.web.HttpRequest
import semmle.python.security.strings.Untrusted

/* Sinks */
import SQL

/** A part of a string that appears to be a SQL command and is thus
 * vulnerable to malicious input.
 */
class SimpleSqlStringInjection extends TaintSink {

    override string toString() { result = "simple SQL string injection" }

    SimpleSqlStringInjection() {
        probable_sql_command(_, this)
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof ExternalStringKind
    }

}


from TaintedPathSource src, TaintedPathSink sink
where src.flowsTo(sink)
select sink.getSink(), src, sink, "This SQL query depends on $@.", src.getSource(), "a user-provided value"

