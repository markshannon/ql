/**
 * @name SQL query built from user-controlled sources
 * @description Building a SQL query from user-controlled sources is vulnerable to insertion of
 *              malicious SQL code by the user.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id py/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 *       external/owasp/owasp-a1
 */

import python
import semmle.python.security.Paths

/* Sources */
import semmle.python.web.HttpRequest

/* Sinks */
import semmle.python.security.injection.Sql
import semmle.python.web.django.Db
import semmle.python.web.django.Model

import SQL

from TaintedPathSource src, TaintedPathSink sink
where src.flowsTo(sink) and not probable_sql_command(sink.getSink(), _)
select sink.getSink(), src, sink, "This SQL query depends on $@.", src.getSource(), "a user-provided value"
