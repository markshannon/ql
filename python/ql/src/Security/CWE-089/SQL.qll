import python


StringObject first_part(ControlFlowNode command) {
    exists(Operator op |
        op = command.(BinaryExprNode).getOp() and
        command.(BinaryExprNode).getLeft().refersTo(result)
        |
        op instanceof Add or op instanceof Mod
    )
    or
    exists(CallNode call, SequenceObject seq |
        call = command |
        call = theStrType().lookupAttribute("join") and
        call.getArg(0).refersTo(seq) and
        seq.getInferredElement(0) = result
    )
}

/**
 * Gets a SQL keyword.
 */
private string sqlKeyword() {
  result = "ALTER" or
  result = "COUNT" or
  result = "CREATE" or
  result = "DATABASE" or
  result = "DELETE" or
  result = "DISTINCT" or
  result = "DROP" or
  result = "FROM" or
  result = "GROUP" or
  result = "INSERT" or
  result = "INTO" or
  result = "LIMIT" or
  result = "ORDER" or
  result = "SELECT" or
  result = "TABLE" or
  result = "UPDATE" or
  result = "WHERE"
}

/**
 * Gets a regular expression that matches a string that likely is a SQL statement.
 */
string sqlPattern() {
  result = ".*(" + concat("\\b" + sqlKeyword() + "\\b", "|") +  ").*"
}

/** Holds if `command` appears to be a SQL command string of which `inject` is a part. */
predicate probable_sql_command(ControlFlowNode command, ControlFlowNode inject) {
    inject = command.getAChild+() and
    first_part(command).getText().regexpMatch(sqlPattern())
}
