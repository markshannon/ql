/**
 * @name RangeSsa correspondence test
 * @description RangeSsa correspondence test. For each reachable definition or parameter there should be a corresponding SSA definition.
 * @kind test
 */

import cpp
import semmle.code.cpp.rangeanalysis.RangeSSA

/* Count of number of reachable definitions or parameters where the no corresponding SSA definition exists.
  Should always be zero *regardless* of the input */

select
count(Variable v, ControlFlowNode def | var_definition(v, def) and not unreachable(def) and
      not exists(RangeSsaDefinition d | d.getAVariable() = v and d.getDefinition() = def)
)
+
count(Parameter p |
      exists(p.getAnAccess())
      and 
      not exists(RangeSsaDefinition d | d.getAVariable() = p and d.getDefinition() = p.getFunction().getEntryPoint())
)
