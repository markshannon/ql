/**
 * @name Reachable Fraction
 * @description Fraction of all control flow nodes deemed reachable by points-to.
 */

import python

import semmle.python.pointsto.PointsTo

predicate actually_reachable(BasicBlock b) {
    PointsToInternal::reachableBlock(b, _)
}

predicate potentially_reachable(BasicBlock b) {
    PointsToInternal::reachableBlock(b.getScope().getEntryNode().getBasicBlock(), _)
}


from int actual, int potential
where
actual = count(BasicBlock b| actually_reachable(b)) and potential = count(BasicBlock b | potentially_reachable(b))
select "Reachable fraction of basic blocks is " + 100.0 * actual /potential + "%", actual, potential

