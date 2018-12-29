import python
private import semmle.python.pointsto.PointsTo

private predicate decorator_call(SourceObject method, ClassObject decorator, FunctionObject func) {
    exists(CallNode f |
        method.getFlowOrigin() = f and
        PointsTo::points_to(f.getFunction(), _, decorator, _, _) and
        PointsTo::points_to(f.getArg(0), _, func, _, _)
    )
}

/** A class method object. Either a decorated function or an explicit call to classmethod(f) */ 
class ClassMethodObject extends SourceObject {

    ClassMethodObject() {
        PointsTo::class_method(this, _)
    }

    FunctionObject getFunction() {
        PointsTo::class_method(this, result)
    }

    CallNode getACall() {
        PointsTo::class_method_call(this, _, _, _, result)
    }

    override boolean isClass() {
        result = false
    }

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

    override ClassObject getAnInferredType() {
        result = theClassMethodType()
    }

    override boolean isComparable() {
        result = true
    }

}

/** A static method object. Either a decorated function or an explicit call to staticmethod(f) */ 
class StaticMethodObject extends SourceObject {

    StaticMethodObject() {
        decorator_call(this, theStaticMethodType(), _)
    }

    FunctionObject getFunction() {
        decorator_call(this, theStaticMethodType(), result)
    }

    override boolean isClass() {
        result = false
    }

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

    override ClassObject getAnInferredType() {
        result = theStaticMethodType()
    }

    override boolean isComparable() {
        result = true
    }

}

