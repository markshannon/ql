import python
private import semmle.python.pointsto.PointsTo

/** A Python property:
 *     @property
 *     def f():
 *         ....
 *
 *  Also any instances of types.GetSetDescriptorType (which are equivalent, but implemented in C)
 */
abstract class PropertyObject extends Object {

    /** Gets the name of this property */
    abstract string getName();

    /** Gets the getter of this property */
    abstract Object getGetter();

    /** Gets the setter of this property */
    abstract Object getSetter();

    /** Gets the deleter of this property */
    abstract Object getDeleter();

    /** Whether this property is read-only. */
    predicate isReadOnly() {
        not exists(this.getSetter()) 
    }

    /** Gets an inferred type of this property.
     * That is the type returned by its getter function,
     * not the type of the property object which is types.PropertyType. */
    abstract ClassObject getInferredPropertyType();

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

}


class PythonPropertyObject extends PropertyObject, SourceObject {

    PythonPropertyObject() {
        property_getter(this.getFlowOrigin(), _)
    }

    override string getName() {
        result = this.getGetter().getName()
    }

    /** Gets the getter function of this property */
    override FunctionObject getGetter() {
         property_getter(this.getFlowOrigin(), result)
    }

    override ClassObject getInferredPropertyType() {
        result = this.getGetter().getAnInferredReturnType()
    }

    /** Gets the setter function of this property */
    override FunctionObject getSetter() {
         property_setter(this.getFlowOrigin(), result)
    }

    /** Gets the deleter function of this property */
    override FunctionObject getDeleter() {
         property_deleter(this.getFlowOrigin(), result)
    }

    override string toString() {
        result = "Property " + this.getName() 
    }

    override boolean isClass() {
        result = false
    }

    override ClassObject getAnInferredType() {
        result = thePropertyType()
    }

    override boolean isComparable() {
        result = true
    }

}

class BuiltinPropertyObject extends PropertyObject, BuiltinObject {

    BuiltinPropertyObject() {
        this.getBuiltinType() = theBuiltinPropertyType()
    }

    override string getName() {
        py_cobjectnames(this.getRaw(), result)
    }

    /** Gets the getter method wrapper of this property */
    override Object getGetter() {
         py_cmembers_versioned(this.getRaw(), "__get__", result.(BuiltinObject).getRaw(), major_version().toString())
    }

    override ClassObject getInferredPropertyType() {
        none()
    }

    /** Gets the setter method wrapper of this property */
    override Object getSetter() {
         py_cmembers_versioned(this.getRaw(), "__set__", result.(BuiltinObject).getRaw(), major_version().toString())
    }

    /** Gets the deleter method wrapper of this property */
    override Object getDeleter() {
         py_cmembers_versioned(this.getRaw(), "__delete__", result.(BuiltinObject).getRaw(), major_version().toString())
    }

    override string toString() {
        result = "Property " + this.getName() 
    }

    override boolean isClass() {
        result = false
    }

}

private predicate property_getter(CallNode decorated, FunctionObject getter) {
    PointsTo::points_to(decorated.getFunction(), _, thePropertyType(), _, _) and
    PointsTo::points_to(decorated.getArg(0), _, getter, _, _)
}

private predicate refersTo(ControlFlowNode f, Object o) {
    PointsTo::points_to(f, _, o, _, _)
}

private predicate property_setter(CallNode decorated, FunctionObject setter) {
    property_getter(decorated, _)
    and
    exists(CallNode setter_call, AttrNode prop_setter, SourceObject decobj |
        refersTo(prop_setter.getObject("setter"), decobj) and
        decorated = decobj.getFlowOrigin() |
        refersTo(setter_call.getArg(0), setter)
        and
        setter_call.getFunction() = prop_setter
    )
    or
    decorated.getFunction().refersTo(thePropertyType())
    and
    decorated.getArg(1).refersTo(setter)
}

private predicate property_deleter(CallNode decorated, FunctionObject deleter) {
    property_getter(decorated, _)
    and
    exists(CallNode deleter_call, AttrNode prop_deleter, SourceObject decobj |
        refersTo(prop_deleter.getObject("deleter"), decobj) and
        decorated = decobj.getFlowOrigin() |
        refersTo(prop_deleter.getObject("deleter"), deleter)
        and
        deleter_call.getFunction() = prop_deleter
    )
    or
    refersTo(decorated.getFunction(), thePropertyType())
    and
    refersTo(decorated.getArg(2), deleter)
}

