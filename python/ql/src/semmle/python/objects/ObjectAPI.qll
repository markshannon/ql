import python
private import TObject
private import semmle.python.objects.ObjectInternal
private import semmle.python.pointsto.PointsTo2
private import semmle.python.pointsto.PointsToContext

class ObjectSource = Object;

class Value extends TObject {

    Value() {
        not this = ObjectInternal::unknown() and
        not this = ObjectInternal::unknownClass() and
        not this = ObjectInternal::undefined()
    }

    string toString() {
        result = this.(ObjectInternal).toString()
    }

    ControlFlowNode getAReference() {
        PointsTo2::points_to(result, _, this, _)
    }

    predicate pointsTo(ControlFlowNode node, PointsToContext context, ControlFlowNode origin) {
        PointsTo2::points_to(node, context, this, origin)
    }

    Value getClass() {
        result = this.(ObjectInternal).getClass()
    }

    CallNode getACall() {
        PointsTo2::points_to(result.getFunction(), _, this, _)
        or
        exists(BoundMethodObjectInternal bm |
            PointsTo2::points_to(result.getFunction(), _, bm, _) and
            bm.getFunction() = this
        )
    }

    Value attr(string name) {
        this.(ObjectInternal).attribute(name, result, _)
    }

    /* For backwards compatibility with old API */
    ObjectSource getSource() {
        result = this.(ObjectInternal).getSource()
    }

    /** Gets the `ControlFlowNode` that will be passed as the nth argument to `this` when called at `call`.
        This predicate will correctly handle `x.y()`, treating `x` as the zeroth argument.
    */
    ControlFlowNode getArgumentForCall(CallNode call, int n) {
        // TO DO..
        none()
    }

    /** Gets the `ControlFlowNode` that will be passed as the named argument to `this` when called at `call`.
        This predicate will correctly handle `x.y()`, treating `x` as the self argument.
    */
    ControlFlowNode getNamedArgumentForCall(CallNode call, string name) {
        // TO DO..
        none()
    }
}

class ModuleValue extends Value {

    ModuleValue() {
        this instanceof ModuleObjectInternal
    }

    predicate exports(string name) {
        not this.(ModuleObjectInternal).attribute("__all__", _, _) and this.(ModuleObjectInternal).attribute(name, _, _)
    }

    string getName() {
        result = this.(ModuleObjectInternal).getName()
    }

}

module Module {

    ModuleValue named(string name) {
        result.getName() = name
    }

}


class CallableValue extends Value {

    CallableValue() {
        this instanceof CallableObjectInternal
    }

    predicate neverReturns() {
        // TO DO..
        none()
    }

}

class ClassValue extends Value {

    ClassValue() {
        this.(ObjectInternal).isClass() = true
    }

}
