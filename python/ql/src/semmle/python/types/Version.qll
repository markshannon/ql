import python
import semmle.python.GuardedControlFlow
private import semmle.python.pointsto.PointsTo


/** DEPRECATED: 
 *  A test on the major version of the Python interpreter 
 * */
class VersionTest extends @py_flow_node {

    string toString() {
        result = "VersionTest"
    }

    VersionTest() {
        PointsTo::version_const(this, _, _)
    }

    predicate isTrue() {
        PointsTo::version_const(this, _, true)
    }

    AstNode getNode() {
        result = this.(ControlFlowNode).getNode()
    }

}

/** A guard on the major version of the Python interpreter */
class VersionGuard extends ConditionBlock {

    VersionGuard() {
        exists(VersionTest v |
            exists(SourceObject vo |
                PointsTo::points_to(this.getLastNode(), _, vo, _, _) and
                vo.getFlowOrigin() = v
            ) or
            PointsTo::points_to(this.getLastNode(), _, _, _, v)
        )
    }

    predicate isTrue() {
        exists(VersionTest v |
            v.isTrue() |
            exists(SourceObject vo |
                PointsTo::points_to(this.getLastNode(), _, vo, _, _) and
                vo.getFlowOrigin() = v
            ) or
            PointsTo::points_to(this.getLastNode(), _, _, _, v)
        )
    }

}

class OsTest extends SourceObject {

    OsTest() {
        isOsTest(this)
    }

    string getOs() {
        os_compare(this.getFlowOrigin(), result)
    }

    override string toString() {
        result = "OsTest"
    }

}

private predicate isOsTest(SourceObject o) {
    os_compare(o.getFlowOrigin(), _)
}


class OsGuard extends ConditionBlock {

    OsGuard() {
        exists(SourceObject t |
            PointsTo::points_to(this.getLastNode(), _, theBoolType(), t, _) and
            isOsTest(t)
        )
    }

    string getOs() {
        exists(SourceObject t |
            PointsTo::points_to(this.getLastNode(), _, theBoolType(), t, _) and result = t.(OsTest).getOs()
        )
    }

}


