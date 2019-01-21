import python
import semmle.python.types.ClassObject
import semmle.python.types.ModuleObject

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

    ControlFlowNode getFlowOrigin() { none() }

    final AstNode getOrigin() {
        result = this.getFlowOrigin().getNode()
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        this.getOrigin().getLocation().hasLocationInfo(filepath, bl, bc, el, ec)
        or
        exists(this.getOrigin()) and filepath = ":Compiled Code" and bl = 0 and bc = 0 and el = 0 and ec = 0
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

    boolean booleanValue() { none() }

    @py_cobject getRaw() {
        none()
    }

}

class BuiltinObject extends Object, TBuiltinObject {

    override @py_cobject getRaw() {
        this = TBuiltinObject(result)
    }

    override string toString() {
        exists(ClassObject type, string typename, string objname |
            py_cobjecttypes(this.getRaw(), type) and 
            py_cobjectnames(this.getRaw(), objname) and 
            typename = type.getName() and
            result = typename + " " + objname
        )
    }

    /** Gets an inferred type for this object, without using inter-procedural analysis.
     * WARNING: The lack of context makes this less accurate than f.refersTo(this, result, _)
     * for a control flow node 'f' */
    override ClassObject getAnInferredType() {
        py_cobjecttypes(this.getRaw(), result)
    }

    override predicate isBuiltin() { any() }

}

class NumericObject extends BuiltinObject {

    NumericObject() {
         py_cobjecttypes(this.getRaw(), theIntType()) or 
         py_cobjecttypes(this.getRaw(), theLongType()) or
         py_cobjecttypes(this.getRaw(), theFloatType())
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

    /** Gets the value of this object if it is a constant integer and it fits in a QL int */ 
    int intValue() {
        (py_cobjecttypes(this.getRaw(), theIntType()) or py_cobjecttypes(this.getRaw(), theLongType()))
        and
        exists(string s | py_cobjectnames(this.getRaw(), s) and result = s.toInt())
    }

    /** Gets the value of this object if it is a constant float */ 
    float floatValue() {
        (py_cobjecttypes(this.getRaw(), theFloatType()))
        and
        exists(string s | py_cobjectnames(this.getRaw(), s) and result = s.toFloat())
    }

}

private abstract class Hidden extends Object {

    override string toString() { none() }

}

class UnknownValue extends TUnknownValue, Hidden {

    override ClassObject getAnInferredType() {
        result = theUnknownType()
    }

}

class UndefinedVariable extends TUndefinedVariable, Hidden {

    override ClassObject getAnInferredType() {
        none()
    }

}

class SourceObject extends TCfgNodeObject, Object {

    override string toString() { 
        result = this.getOrigin().toString()
    }


    override ControlFlowNode getFlowOrigin() {
        this = TCfgNodeObject(result)
    }

    override ClassObject getAnInferredType() {
        exists(ControlFlowNode somewhere | somewhere.refersTo(this.getFlowOrigin(), result, _))
    }

}

class StringObject extends BuiltinObject {

    StringObject() {
        py_cobjecttypes(this.getRaw(), theUnicodeType()) or
        py_cobjecttypes(this.getRaw(), theBytesType())
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

    /** Gets the text for this string */
    cached string getText() {
        exists(string quoted_string |
            py_cobjectnames(this.getRaw(), quoted_string) and
            result = quoted_string.regexpCapture("[bu]'([\\s\\S]*)'", 1)
        )
    }

}


/** Sequence objects (lists and tuples)
 *  Includes those occurring in the source as a literal
 *  or in a builtin module as a value.
 */
abstract class SequenceObject extends Object {

    /** Gets the length of this sequence */
    abstract int getLength();

    abstract Object getInferredElement(int n);

}

abstract class BuiltinSequenceObject extends SequenceObject, BuiltinObject {

    /** Gets the nth item of this builtin sequence */
    Object getBuiltinElement(int n) {
        py_citems(this.getRaw(), n, result.getRaw())
    }

    override Object getInferredElement(int n) {
        result = this.getBuiltinElement(n)
    }

    override int getLength() {
        result = strictcount(this.getBuiltinElement(_))
    }

}

abstract class SourceSequenceObject extends SequenceObject, SourceObject {

    /** Gets the nth source element of this sequence */
    ControlFlowNode getSourceElement(int n) {
        result = this.getFlowOrigin().(SequenceNode).getElement(n)
    }

    override Object getInferredElement(int n) {
        this.getSourceElement(n).refersTo(result)
    }

    override int getLength() {
        result = strictcount(this.getSourceElement(_))
    }

}

class BuiltinTupleObject extends BuiltinSequenceObject {

    BuiltinTupleObject() {
        py_cobjecttypes(this.(BuiltinObject).getRaw(), theTupleType())
    }

}

class SourceTupleObject extends SourceSequenceObject {

    SourceTupleObject() {
        this.getFlowOrigin() instanceof TupleNode
        or
        exists(Function func | func.getVararg().getAFlowNode() = this.getFlowOrigin())
    }

}

class BuiltinListObject extends BuiltinSequenceObject {

    BuiltinListObject() {
        py_cobjecttypes(this.(BuiltinObject).getRaw(), theListType())
    }

}

class SourceListObject extends SourceSequenceObject {

    SourceListObject() {
        this.getFlowOrigin() instanceof ListNode
        or
        exists(Function func | func.getVararg().getAFlowNode() = this.getFlowOrigin())
    }

}

class NonEmptyTupleObject extends SequenceObject, TNonEmptyTuple {

    override boolean booleanValue() {
        result = true
    }

    override int getLength() { none() }

    override Object getInferredElement(int n) { none() }

    override string toString() { result = "Non-empty tuple" }

    override ClassObject getAnInferredType() { result = theTupleType() }

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

    Folder getFolder() {
        this = TPackage(result)
    }

    ModuleObject submodule(string name) {
        this.getName() + "." + name = result.getName()
    }

    PythonModuleObject getInitModule() {
        result.getModule().getFile() = this.getFolder().getFile("__init__.py")
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

