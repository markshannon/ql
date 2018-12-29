import python
private import semmle.python.pointsto.Base
import semmle.python.types.ClassObject
import semmle.python.types.ModuleObject
private import semmle.python.pointsto.PointsTo
private import semmle.python.pointsto.PointsToContext

private newtype TObject =
    TBuiltinObject(@py_cobject raw) {
        not (
            /* @py_cobjects for modules which have a corresponding Python module */
            exists(@py_cobject mod_type | py_special_objects(mod_type, "ModuleType") and 
            py_cobjecttypes(raw, mod_type)) and
            exists(Module m | py_cobjectnames(raw, m.getName()))
        )
    }
    or
    TCfgNodeObject(@py_object obj) {
        not obj.(ControlFlowNode).getNode() instanceof ImmutableLiteral
    }
    or
    TUnknownValue()
    or
    TUndefinedVariable()
    or
    TUnknownClass()
    or
    TNonEmptyTuple()
    or
    TPackage(Folder folder) {
        exists(folder.getModuleName())
    }
    or
    TSuperInstance(Object self, ClassObject start) {
        exists(CallNode call, PointsToContext context |
            PointsTo::points_to(call.getFunction(), context, theSuperType(), _, _)
            |
            PointsTo::points_to(call.getArg(0), context, start, _, _) and
            PointsTo::points_to(call.getArg(1), context, self, _, _)
            or
            major_version() = 3 and
            not exists(call.getArg(0)) and
            exists(Function func |
                call.getScope() = func and
                context.appliesToScope(func) and
                /* Implicit class argument is lexically enclosing scope */
                func.getScope() = start.getPyClass() and
                /* Implicit 'self' is the 0th parameter */
                self.(SourceObject).getFlowOrigin() = func.getArg(0).asName().getAFlowNode()
            )
        )
    }
    or
    TBoundMethod(AttrNode binding, FunctionObject method, Object self) {
        exists(ClassObject cls, string name |
            PointsTo::points_to(binding.getObject(name), _, self, cls, _) and
            cls.lookupAttribute(name) = method and
            self.isClass() = false
        )
    }


abstract class Object extends TObject {

    abstract string toString();

    /** Gets an inferred type for this object, without using inter-procedural analysis.
     * WARNING: The lack of context makes this less accurate than f.refersTo(this, result, _)
     * for a control flow node 'f' */
    abstract ClassObject getAnInferredType();

    predicate isBuiltin() { none() }

    /** Retained for backwards compatibility. See Object.isBuiltin() */
    deprecated predicate isC() {
        this.isBuiltin()
    }

    private
    ClassObject declaringClass(string name) {
        result.declaredAttribute(name) = this
    }

    /** Whether this overrides o. In this context, "overrides" means that this object
     *  is a named attribute of a some class C and `o` is a named attribute of another
     *  class S, both attributes having the same name, and S is a super class of C.
     */
    predicate overrides(Object o) {
        exists(string name |
            declaringClass(name).getASuperType() = o.declaringClass(name)
        )
    }

    abstract boolean booleanValue();

    abstract predicate maybe();

    abstract boolean isClass();

    /** Holds if meaningful comparisons can be made with `o`.
     * True for basic objects like 3 or None.
     */
    abstract boolean isComparable();

}

/** Gets the pseudo-object representing an unknown value */
Object unknownValue() {
    result = TUnknownValue()
 
}

abstract class BuiltinObject extends Object, TBuiltinObject {

    @py_cobject getRaw() {
        this = TBuiltinObject(result)
    }

    override string toString() {
        exists(BuiltinClassObject type, string typename, string objname |
            py_cobjecttypes(this.getRaw(), type.getRaw()) and
            py_cobjectnames(this.getRaw(), objname) and
            typename = type.getName() and
            result = typename + " " + objname
        )
    }

    /** Gets an inferred type for this object, without using inter-procedural analysis.
     * WARNING: The lack of context makes this less accurate than f.refersTo(this, result, _)
     * for a control flow node 'f' */
    override ClassObject getAnInferredType() {
        py_cobjecttypes(this.getRaw(), result.(BuiltinClassObject).getRaw())
    }

    override predicate isBuiltin() { any() }

    ClassObject getBuiltinType() {
        py_cobjecttypes(this.getRaw(), result.(BuiltinClassObject).getRaw())
    }

    string getName() {
        py_cobjectnames(this.getRaw(), result)
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        filepath = ":Compiled Code" and bl = 0 and bc = 0 and el = 0 and ec = 0
    }

    override boolean isComparable() {
        result = true
    }

}

class NumericObject extends BuiltinObject {

    NumericObject() {
         py_cobjecttypes(this.getRaw(), theIntType().getRaw()) or 
         py_cobjecttypes(this.getRaw(), theLongType().getRaw()) or
         py_cobjecttypes(this.getRaw(), theFloatType().getRaw())
    }

    /** Gets the Boolean value that this object
     *  would evaluate to in a Boolean context,
     * such as `bool(x)` or `if x: ...`
     */
    override boolean booleanValue() {
        this.intValue() != 0 and result = true
        or
        this.intValue() = 0 and result = false
        or
        this.floatValue() != 0 and result = true
        or
        this.floatValue() = 0 and result = false
    }

    override predicate maybe() { none() }

    /** Gets the value of this object if it is a constant integer and it fits in a QL int */ 
    int intValue() {
        (py_cobjecttypes(this.getRaw(), theIntType().getRaw()) or py_cobjecttypes(this.getRaw(), theLongType().getRaw()))
        and
        exists(string s | py_cobjectnames(this.getRaw(), s) and result = s.toInt())
    }

    /** Gets the value of this object if it is a constant float */ 
    float floatValue() {
        (py_cobjecttypes(this.getRaw(), theFloatType().getRaw()))
        and
        exists(string s | py_cobjectnames(this.getRaw(), s) and result = s.toFloat())
    }

    override boolean isClass() { result = false }

}

private abstract class Hidden extends Object {

    override string toString() { none() }

    override boolean isClass() { none() }

}

class UnknownValue extends TUnknownValue, Hidden {

    override ClassObject getAnInferredType() {
        result = theUnknownType()
    }

    override predicate maybe() { any() }

    override boolean isComparable() {
        result = false
    }

    override boolean booleanValue() { none() }
}

class UndefinedVariable extends TUndefinedVariable, Hidden {

    override ClassObject getAnInferredType() {
        none()
    }

    override predicate maybe() { any() }

    override boolean isComparable() {
        result = false
    }

    override boolean booleanValue() { none() }

}

abstract class SourceObject extends TCfgNodeObject, Object {

    override string toString() { 
        result = this.getOrigin().toString()
    }

    final AstNode getOrigin() {
        result = this.getFlowOrigin().getNode()
    }

    ControlFlowNode getFlowOrigin() {
        this = TCfgNodeObject(result)
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        this.getOrigin().getLocation().hasLocationInfo(filepath, bl, bc, el, ec)
    }

}

class StringObject extends BuiltinObject {

    StringObject() {
        py_cobjecttypes(this.getRaw(), theUnicodeType().getRaw()) or
        py_cobjecttypes(this.getRaw(), theBytesType().getRaw())
    }

    /** Whether this string is composed entirely of ascii encodable characters */
    predicate isAscii() {
        this.getText().regexpMatch("^\\p{ASCII}*$")
    }

    override boolean booleanValue() {
        this.getText() = "" and result = false
        or
        this.getText() != "" and result = true
    }

    override predicate maybe() { none() }

    /** Gets the text for this string */
    cached string getText() {
        exists(string quoted_string |
            py_cobjectnames(this.getRaw(), quoted_string) and
            result = quoted_string.regexpCapture("[bu]'([\\s\\S]*)'", 1)
        )
    }

    override boolean isClass() { result = false }
}


/** Sequence objects (lists and tuples)
 *  Includes those occurring in the source as a literal
 *  or in a builtin module as a value.
 */
abstract class SequenceObject extends Object {

    /** Gets the length of this sequence */
    abstract int getLength();

    abstract Object getElement(int n);

    /** DEPRECATED -- Use `getElement(int n)` instead */
    deprecated final Object getInferredElement(int n) {
        result = this.getElement(n)
    }

    override boolean isClass() { result = false }

}

abstract class BuiltinSequenceObject extends SequenceObject, BuiltinObject {

    /** Gets the nth item of this builtin sequence */
    BuiltinObject getBuiltinElement(int n) {
        py_citems(this.getRaw(), n, result.getRaw())
    }

    override Object getElement(int n) {
        result = this.getBuiltinElement(n)
    }

    override int getLength() {
        exists(@py_cobject raw |
            raw = this.getRaw() and
            result = strictcount(int n | py_citems(raw, n, _))
        )
    }

    override boolean booleanValue() { 
        this.getLength() = 0 and result = false
        or
        this.getLength() != 0 and result = true
    }

}

abstract class SourceSequenceObject extends SequenceObject, SourceObject {

    /** Gets the nth source element of this sequence */
    ControlFlowNode getSourceElement(int n) {
        result = this.getFlowOrigin().(SequenceNode).getElement(n)
    }

    override Object getElement(int n) {
        PointsTo::points_to(this.getSourceElement(n), _, result, _, _)
    }

    override int getLength() {
        exists(SequenceNode node |
            node = this.getFlowOrigin() |
            result = strictcount(node.getElement(_))
        )
    }

    override boolean booleanValue() { 
        this.getLength() = 0 and result = false
        or
        this.getLength() != 0 and result = true
    }

    override boolean isComparable() {
        result = true
    }

}

abstract class TupleObject extends SequenceObject {

}

class BuiltinTupleObject extends BuiltinSequenceObject, TupleObject {

    BuiltinTupleObject() {
        py_cobjecttypes(this.(BuiltinObject).getRaw(), theTupleType().getRaw())
    }

    override predicate maybe() { none() }

}

class SourceTupleObject extends SourceSequenceObject, TupleObject {

    SourceTupleObject() {
        this.getFlowOrigin() instanceof TupleNode
        or
        exists(Function func | func.getVararg().getAFlowNode() = this.getFlowOrigin())
    }

    override predicate maybe() { none() }

    override ClassObject getAnInferredType() {
        result = theTupleType()
    }

}

class BuiltinListObject extends BuiltinSequenceObject {

    BuiltinListObject() {
        this.getBuiltinType() = theListType()
    }

    override predicate maybe() { none() }

}

class SourceListObject extends SourceSequenceObject {

    SourceListObject() {
        this.getFlowOrigin() instanceof ListNode
        or
        exists(Function func | func.getVararg().getAFlowNode() = this.getFlowOrigin())
    }

    override predicate maybe() { none() }

    override ClassObject getAnInferredType() {
        result = theListType()
    }

}

class NonEmptyTupleObject extends TupleObject, TNonEmptyTuple {

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

    override int getLength() { none() }

    override Object getElement(int n) { none() }

    override string toString() { result = "Non-empty tuple" }

    override ClassObject getAnInferredType() { result = theTupleType() }

    override boolean isComparable() {
        result = false
    }

}

class PackageObject extends ModuleObject, TPackage {

    override ClassObject getAnInferredType() {
        result = theModuleType()
    }

    override string getName() {
        exists(Folder f |
            this = TPackage(f) and
            result = f.getModuleName()
        )
    }

    ModuleObject submodule(string name) {
        this.getName() + "." + name = result.getName()
    }

    PythonModuleObject getInitModule() {
        result.getModule().getFile() = this.getPath().getFile("__init__.py")
    }

    predicate hasNoInitModule() {
        exists(Folder path | 
            this = TPackage(path) and
            not exists(path.getFile("__init__.py"))
        )
    }

    override Container getPath() {
        this = TPackage(result)
    }

    override Object getAttribute(string name) {
        PointsTo::package_attribute_points_to(this, name, result, _, _)
    }

    override predicate exportsComplete() {
        not exists(this.getInitModule())
        or
        this.getInitModule().exportsComplete()
    }

    override predicate hasAttribute(string name) {
        exists(this.submodule(name))
        or
        this.getInitModule().hasAttribute(name)
    }

    override predicate attributeRefersTo(string name, Object value, Origin origin) {
        PointsTo::package_attribute_points_to(this, name, value, _, origin)
    }

    override predicate attributeRefersTo(string name, Object value, ClassObject cls, Origin origin) {
        PointsTo::package_attribute_points_to(this, name, value, cls, origin)
    }

    Location getLocation() {
        none()
    }

    predicate hasLocationInfo(string path, int bl, int bc, int el, int ec) {
        path = this.getPath().getName() and
        bl = 0 and bc = 0 and el = 0 and ec = 0
    }

    override Module getModule() {
        none()
    }

    override boolean isComparable() {
        result = true
    }

}


class SuperInstance extends Object, TSuperInstance {

    override ClassObject getAnInferredType() {
        result = theSuperType()
    }

    override string toString() {
        result = "super()"
    }

    Object getSelf() {
        TSuperInstance(result, _) = this
    }

    ClassObject getStartType() {
        TSuperInstance(_, result) = this
    }

    override boolean isClass() { result = false }

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

    override boolean isComparable() {
        result = false
    }

}

class UnknownType extends ClassObject, TUnknownClass {

    override string toString() { none() }

    override string getName() {
        none()
    }

    override string getQualifiedName() {
        none()
    }

    override predicate maybe() { none() }

    override ClassObject getAnInferredType() {
        result = this
    }

    override boolean isComparable() {
        result = false
    }

    override boolean declaresAttributeBoolean(string name) {
        none()
    }

}

/* Efficient version for speed */
//
//library class Origin extends @py_object {
//
//    Origin() {
//        this instanceof ControlFlowNode
//        or
//        /* Unknown origin */
//        py_special_objects(this, "_2")
//    }
//
//    string toString() {
//        /* Not to be displayed */
//        none()
//    }
//
//    ControlFlowNode asFlowNode() {
//        result = this
//    }
//
//    pragma[inline]
//    ControlFlowNode asFlowNode(ControlFlowNode here) {
//        result = this
//        or
//        py_special_objects(this, "_2") and result = here
//    }
//
//}

/* ADT version to make implicit conversions compiler errors */



/** The `builtin` module */
BuiltinModuleObject theBuiltinModuleObject() {
    result.getRaw() = rawBuiltinModuleObject()
}

private @py_cobject rawBuiltinModuleObject() {
    py_special_objects(result, "builtin_module_2") and major_version() = 2
    or
    py_special_objects(result, "builtin_module_3") and major_version() = 3
}

/** The `sys` module */
BuiltinModuleObject theSysModuleObject() {
    py_special_objects(result.getRaw(), "sys")
}

BuiltinObject builtin_object(string name) {
    py_cmembers_versioned(theBuiltinModuleObject().getRaw(), name, result.getRaw(), major_version().toString())
}

@py_cobject raw_builtin_object(string name) {
    py_cmembers_versioned(rawBuiltinModuleObject(), name, result, major_version().toString())
}

/** The built-in object None */
BuiltinObject theNoneObject() {
    py_special_objects(result.getRaw(), "None")
}

/** The built-in object True */
BuiltinObject theTrueObject() {
    py_special_objects(result.getRaw(), "True")
}

/** The built-in object False */
BuiltinObject theFalseObject() {
    py_special_objects(result.getRaw(), "False")
}

/** The builtin function apply (Python 2 only) */
Object theApplyFunction() {
    result = builtin_object("apply")
}

/** The builtin function hasattr */
Object theHasattrFunction() {
    result = builtin_object("hasattr")
}

/** The builtin function len */
 Object theLenFunction() {
    result = builtin_object("len")
}

/** The builtin function format */
 Object theFormatFunction() {
    result = builtin_object("format")
}

/** The builtin function open */
 Object theOpenFunction() {
    result = builtin_object("open")
}

/** The builtin function print (Python 2.7 upwards) */
 Object thePrintFunction() {
    result = builtin_object("print")
}

/** The builtin function input (Python 2 only) */
 Object theInputFunction() {
    result = builtin_object("input")
}

/** The builtin function locals */
BuiltinObject theLocalsFunction() {
    py_special_objects(result.getRaw(), "locals")
}

/** The builtin function globals */
BuiltinObject theGlobalsFunction() {
    py_special_objects(result.getRaw(), "globals")
}

/** The builtin function sys.exit */
BuiltinObject theExitFunctionObject() {
    py_cmembers_versioned(theSysModuleObject().getRaw(), "exit", result.getRaw(), major_version().toString())
}

/** The NameError class */
Object theNameErrorType() {
    result = builtin_object("NameError")
}

/** The StandardError class */
Object theStandardErrorType() {
    result = builtin_object("StandardError")
}

/** The IndexError class */
Object theIndexErrorType() {
    result = builtin_object("IndexError")
}

/** The LookupError class */
Object theLookupErrorType() {
    result = builtin_object("LookupError")
}

/** The named quitter object (quit or exit) in the builtin namespace */
Object quitterObject(string name) {
    (name = "quit" or name = "exit") and
    result = builtin_object(name)
}

/** The builtin object `NotImplemented`. Not be confused with `NotImplementedError`. */
Object theNotImplementedObject() {
    result = builtin_object("NotImplemented")
}

BuiltinObject theEmptyTupleObject() {
    exists(@py_cobject raw |
        raw = result.getRaw() |
        py_cobjecttypes(raw, theTupleType().getRaw()) and not py_citems(raw, _, _)
    )
}

Object theUnknownType() {
    result instanceof UnknownType
}


/** A Version of the Python interpreter.
 * Currently only 2.7 or 3.x but may include different sets of versions in the future. */
class Version extends int {

    Version() {
        this = 2 or this = 3
    }

    /** Holds if this version (or set of versions) includes the version `major`.`minor` */
    predicate includes(int major, int minor) {
        this = 2 and major = 2 and minor = 7
        or
        this = 3 and major = 3 and minor in [4..7]
    }

}

BuiltinObject theSysVersionInfoTuple() {
    py_cmembers_versioned(theSysModuleObject().getRaw(), "version_info", result.getRaw(), major_version().toString())
}

BuiltinObject theSysHexVersionNumber() {
    py_cmembers_versioned(theSysModuleObject().getRaw(), "hexversion", result.getRaw(), major_version().toString())
}

BuiltinObject theSysVersionString() {
    py_cmembers_versioned(theSysModuleObject().getRaw(), "version", result.getRaw(), major_version().toString())
}


string reversed(Cmpop op) {
    op instanceof Lt and result = ">"
    or
    op instanceof Gt and result = "<"
    or
    op instanceof GtE and result = "<="
    or
    op instanceof LtE and result = ">="
    or
    op instanceof Eq and result = "=="
    or
    op instanceof NotEq and result = "!="
}

string os_name(StrConst s) {
    exists(string t | 
        t = s.getText() |
        t = "Darwin" and result = "darwin"
        or
        t = "Windows" and result = "win32"
        or
        t = "Linux" and result = "linux"
        or
        not t = "Darwin" and not t = "Windows" and not t = "Linux" and result = t
    )
}

predicate get_platform_name(Expr e) {
    exists(Attribute a, Name n | a = e and n = a.getObject() |
        n.getId() = "sys" and a.getName() = "platform"
    )
        or
    exists(Call c, Attribute a, Name n | 
        c = e and a = c.getFunc() and n = a.getObject() |
        a.getName() = "system" and n.getId() = "platform"
    )
}

predicate os_compare(ControlFlowNode f, string name) {
    exists(Compare c, Expr l, Expr r, Cmpop op |
        c = f.getNode() and
        l = c.getLeft() and
        r = c.getComparator(0) and
        op = c.getOp(0) |
        (op instanceof Eq or op instanceof Is)
        and
        ( get_platform_name(l) and name = os_name(r)
          or
          get_platform_name(r) and name = os_name(l)
        )
    )
}

/** A bound method object, x.f where type(x) has a method f */
class BoundMethod extends Object, TBoundMethod {

    /* Gets the method 'f' in 'x.f' */
    FunctionObject getMethod() {
        this = TBoundMethod(_, result, _)
    }

    override boolean isClass() {
        result = false
    }

    override boolean booleanValue() { result = true }

    override predicate maybe() { none() }

    override string toString() { result = "bound method" }

    override ClassObject getAnInferredType() { result = theBoundMethodType() }

    override boolean isComparable() {
        result = false
    }

}

