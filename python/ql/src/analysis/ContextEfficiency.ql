/** Compute the total points-to facts, the total size of the points-to relation and 
 * the ratio of the two in relation to the depth of context.
 */


import python
import semmle.python.pointsto.PointsTo
import semmle.python.pointsto.PointsToContext

from int total_facts, int total_size, int depth, float efficiency
where 
total_facts = strictcount(ControlFlowNode f, Value value |
    exists(PointsToContext ctx |
        PointsTo::pointsTo(f, ctx, value, _) and
        depth = ctx.getDepth()
    )
)
and
total_size = strictcount(ControlFlowNode f, Value value, PointsToContext ctx, ControlFlowNode orig |
    PointsTo::pointsTo(f, ctx, value, orig) and
    depth = ctx.getDepth()
)
and
efficiency = 100.0 * total_facts / total_size
select depth, total_facts, total_size, efficiency
