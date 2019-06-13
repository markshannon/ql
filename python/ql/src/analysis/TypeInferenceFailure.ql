/**
 * @name Type inference fails for 'object'
 * @description Type inference fails for 'object' which reduces recall for many queries.
 * @kind problem
 * @problem.severity info
 * @id py/type-inference-failure
 * @deprecated
 */
import python


from ControlFlowNode f, Value o
where f.pointsTo(o) and
not exists(o.getClass())
select o, "Type inference fails for 'object'."