import python
private import semmle.python.pointsto.Base
private import semmle.python.pointsto.PointsTo
private import semmle.python.types.Builtins

private newtype TObject =
    TBuiltinObject(Builtin bltn) { any() }
    or
    TSourceObject(ControlFlowNode obj, TObject cls) {
        not obj.(ControlFlowNode).getNode() instanceof ImmutableLiteral
        and
        (
            obj.getNode() instanceof CallableExpr and cls = thePyFunctionType()
            or
            cls = simpleClass(obj.getNode())
            or
            PointsTo::instantiation(obj, _, cls)
            or
            kwargs_points_to(obj, cls)
            or
            varargs_points_to(obj, cls)
            or
            obj.isClass() and cls = theUnknownType()
            or
            exists(BuiltinCallable b |
                obj = PointsTo::get_a_call(b, _) and
                cls = b.getAReturnType()
            )
            or
            exists(PyFunctionObject func |
                obj = PointsTo::get_a_call(func, _) and
                func.getFunction().isGenerator() and
                cls = theGeneratorType()
            )
            or
            obj.getNode().(Parameter).isSelf() and
            exists(FunctionObject meth, Function scope |
                meth.getFunction() = scope |
                obj.getScope() = scope and
                scope.getScope() = cls.(ClassObject).getPyClass()
            )
        )
    }


/** Gets the class of this object for simple cases, namely constants, functions, 
 * comprehensions and built-in objects.
 *
 *  This exists primarily for internal use. Use getAnInferredType() instead.
 */
private ClassObject simpleClass(AstNode obj) {
    result = comprehension(obj)
    or
    result = collection_literal(obj)
    or
    result = string_literal(obj)
    or
    obj instanceof CallableExpr and result = thePyFunctionType()
    or
    obj instanceof Module and result = theModuleType()
}


library class ClassDecl extends @py_object {

    ClassDecl() {
        this.(Builtin).isClass() and not this = Builtin::unknownType()
        or
        this.(ControlFlowNode).isClass()
    }

    string toString() {
        result = "ClassDecl"
    }

    predicate declaresAttribute(string name) {
        exists(this.(Builtin).getMember(name))
        or
        exists(Class cls |
            cls.getParent() = this.(ControlFlowNode).getNode() |
            exists(SsaVariable var | name = var.getId() and var.getAUse() = cls.getANormalExit())
        )
    }
}

/** Instances of this class represent objects in the Python program. However, since
 *  the QL database is static and Python programs are dynamic, there are necessarily a
 *  number of approximations. 
 *
 *  Each point in the control flow graph where a new object can be created is treated as
 *  an object. Many builtin objects, such as integers, strings and builtin classes, are 
 *  also treated as 'objects'. Hence each 'object', that is an instance of this class, 
 *  represents a set of actual Python objects in the actual program. 
 *
 *  Ideally each set would contain only one member, but that is not possible in practice. 
 *  Many instances of this class will represent many actual Python objects, especially 
 *  if the point in the control flow graph to which they refer is in a loop. Others may not 
 *  refer to any objects. However, for many important objects such as classes and functions, 
 *  there is a one-to-one relation.
 */
class Object extends TObject {

    /** Gets an inferred type for this object, without using inter-procedural analysis.
     * WARNING: The lack of context makes this less accurate than f.refersTo(this, result, _)
     * for a control flow node 'f' */
    ClassObject getAnInferredType() {
        exists(ControlFlowNode somewhere | somewhere.refersTo(this, result, _))
        or
        this.asBuiltin().getClass() = result.asBuiltin()and not this = unknownValue()
        or
        this = unknownValue() and result = theUnknownType()
    }

    /** Whether this a builtin object. A builtin object is one defined by the implementation, 
        such as the integer 4 or by a native extension, such as a NumPy array class. */
    predicate isBuiltin() {
        exists(this.asBuiltin())
    }

    /** Retained for backwards compatibility. See Object.isBuiltin() */
    predicate isC() {
        this.isBuiltin()
    }

    /** Gets the point in the source code from which this object "originates".
     *
     *  WARNING: The lack of context makes this less accurate than f.refersTo(this, _, result)
     * for a control flow node 'f'.
     */
    AstNode getOrigin() {
        result = this.getCfgNode().getNode()
    }

    private predicate hasOrigin() {
        this = TSourceObject(_, _)
    }

    ControlFlowNode getCfgNode() {
        this = TSourceObject(result, _)
    }

    predicate hasLocationInfo(string filepath, int bl, int bc, int el, int ec) {
        this.hasOrigin() and this.getOrigin().getLocation().hasLocationInfo(filepath, bl, bc, el, ec)
        or
        not this.hasOrigin() and filepath = ":Compiled Code" and bl = 0 and bc = 0 and el = 0 and ec = 0
    }

    /** INTERNAL -- Do not use */
    Builtin asBuiltin() {
        this = TBuiltinObject(result)
    }

    string toString() {
        result = this.asBuiltin().toString()
        or
        result = this.getOrigin().toString()
    }

    /** Gets the class of this object for simple cases, namely constants, functions, 
     * comprehensions and built-in objects.
     *
     *  This exists primarily for internal use. Use getAnInferredType() instead.
     */
    cached ClassObject simpleClass() {
        result = comprehension(this.getOrigin())
        or
        result = collection_literal(this.getOrigin())
        or
        result = string_literal(this.getOrigin())
        or
        this.getOrigin() instanceof CallableExpr and result = thePyFunctionType()
        or
        this.getOrigin() instanceof Module and result = theModuleType()
        or
        result.(Object).asBuiltin() = this.asBuiltin().getClass()
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

    /** The Boolean value of this object if it always evaluates to true or false.
     * For example:
     *     false for None, true for 7 and no result for int(x)
     */
    boolean booleanValue() {
        this = theNoneObject() and result = false 
        or
        this = theTrueObject() and result = true 
        or
        this = theFalseObject() and result = false 
        or
        this = TupleObject::empty() and result = false 
        or
        exists(Tuple t | t = this.getOrigin() |
            exists(t.getAnElt()) and result = true
            or
            not exists(t.getAnElt()) and result = false
        )
        or
        exists(Unicode s | s.getLiteralObject() = this |
            s.getS() = "" and result = false
            or
            s.getS() != "" and result = true
        )
        or
        exists(Bytes s | s.getLiteralObject() = this |
            s.getS() = "" and result = false
            or
            s.getS() != "" and result = true
        )
        or
        exists(Builtin b | b = this.asBuiltin() | b.isClass()) and result = true
        or
        exists(ControlFlowNode f | TSourceObject(f, _) = this | f.isClass()) and result = true
        or
        exists(Module m | m.getEntryNode() = this.getCfgNode()) and result = true
        or
        this.asBuiltin().isModule() and result = true
        or
        this instanceof NonEmptyTupleObject and result = true
        or
        this.(NumericObject).intValue() != 0 and result = true
        or
        this.(NumericObject).intValue() = 0 and result = false
        or
        this.(NumericObject).floatValue() != 0 and result = true
        or
        this.(NumericObject).floatValue() = 0 and result = false
        or
        this.(StringObject).getText() = "" and result = false
        or
        this.(StringObject).getText() != "" and result = true
    }

    predicate notClass() {
        exists(Builtin b | b = this.asBuiltin() | not b.isClass())
        or
        exists(ControlFlowNode f | f = this.getCfgNode() | not f.isClass())
    }

    /** Holds if this object can be referred to by `longName`
     * For example, the modules `dict` in the `sys` module
     * has the long name `sys.modules` and the name `os.path.join`
     * will refer to the path joining function even though it might
     * be declared in the `posix` or `nt` modules.
     * Long names can have no more than three dots after the module name.
     */
    cached predicate hasLongName(string longName) {
        this = findByName0(longName) or
        this = findByName1(longName) or
        this = findByName2(longName) or
        this = findByName3(longName) or
        exists(ClassMethodObject cm |
            cm.hasLongName(longName) and
            cm.getFunction() = this
        )
        or
        exists(StaticMethodObject cm |
            cm.hasLongName(longName) and
            cm.getFunction() = this
        )
    }

    ClassDecl getClassDeclaration() {
        result = this.asBuiltin()
        or
        result = this.getCfgNode()
    }

    predicate isInstance() {
        exists(ClassObject cls, ControlFlowNode src |
            this = TSourceObject(_, cls) and
            src = this.getCfgNode() and
            not src instanceof ClassDecl and
            cls != theModuleType()
        )
    }

   predicate maybe() {
       this.isInstance()
   }

}

private Object findByName0(string longName) {
    result.(ModuleObject).getName() = longName
}

private Object findByName1(string longName) {
    exists(string owner, string attrname |
        longName = owner + "." + attrname
        |
        result = findByName0(owner).(ModuleObject).attr(attrname)
        or
        result = findByName0(owner).(ClassObject).lookupAttribute(attrname)
    )
    and
    not result = findByName0(_)
}

private Object findByName2(string longName) {
    exists(string owner, string attrname |
        longName = owner + "." + attrname
        |
        result = findByName1(owner).(ModuleObject).attr(attrname)
        or
        result = findByName1(owner).(ClassObject).lookupAttribute(attrname)
    )
    and not result = findByName0(_)
    and not result = findByName1(_)
}

private Object findByName3(string longName) {
    exists(string owner, string attrname |
        longName = owner + "." + attrname
        |
        result = findByName2(owner).(ModuleObject).attr(attrname)
        or
        result = findByName2(owner).(ClassObject).lookupAttribute(attrname)
    )
    and not result = findByName0(_)
    and not result = findByName1(_)
    and not result = findByName2(_)
}


/** Numeric objects (ints and floats). 
 *  Includes those occurring in the source as a literal
 *  or in a builtin module as a value.
 */
class NumericObject extends Object {

    NumericObject() {
        this.asBuiltin().getClass() = theIntType().asBuiltin() or
        this.asBuiltin().getClass() = theLongType().asBuiltin() or
        this.asBuiltin().getClass() = theFloatType().asBuiltin()
    }

    /** Gets the value of this object if it is a constant integer and it fits in a QL int */ 
    int intValue() {
        (
            this.asBuiltin().getClass() = theIntType().asBuiltin() or
            this.asBuiltin().getClass() = theLongType().asBuiltin()
        )
        and
        result = this.asBuiltin().getName().toInt()
    }

    /** Gets the value of this object if it is a constant float */ 
    float floatValue() {
        this.asBuiltin().getClass() = theFloatType().asBuiltin()
        and
        result = this.asBuiltin().getName().toFloat()
    }

    /** Gets the string representation of this object, equivalent to calling repr() in Python */
    string repr() {
        exists(string s |
            s = this.asBuiltin().getName() |
            if this.asBuiltin().getClass() = theLongType().asBuiltin() then
                result = s + "L"
            else
                result = s
        )
    }

}

/** String objects (unicode or bytes).
 *  Includes those occurring in the source as a literal
 *  or in a builtin module as a value.
 */
class StringObject extends Object {

    StringObject() {
        this.asBuiltin().getClass() = theUnicodeType().asBuiltin() or
        this.asBuiltin().getClass() = theBytesType().asBuiltin()
    }

    /** Whether this string is composed entirely of ascii encodable characters */
    predicate isAscii() {
        this.getText().regexpMatch("^\\p{ASCII}*$")
    }

    /** Gets the text for this string */
    cached string getText() {
        exists(string quoted_string |
            quoted_string = this.asBuiltin().getName()
            and
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
    int getLength() {
        exists(Builtin b |
            b = this.asBuiltin() and
            result = strictcount(int n | exists(b.getItem(n)))
        )
        or
        exists(SequenceNode s |
            s = this.getCfgNode() |
            result = strictcount(int n | exists(s.getElement(n)))
        )
    }

    /** Gets the nth item of this builtin sequence */
    Object getBuiltinElement(int n) {
        result.asBuiltin() = this.asBuiltin().getItem(n)
    }

    /** Gets the nth source element of this sequence */
    ControlFlowNode getSourceElement(int n) {
        result = this.getCfgNode().(SequenceNode).getElement(n)
    }

    Object getInferredElement(int n) {
        result = this.getBuiltinElement(n)
        or
        this.getSourceElement(n).refersTo(result)
    }

}

class TupleObject extends SequenceObject {

    TupleObject() {
        this.asBuiltin().getClass() = theTupleType().asBuiltin()
        or
        this.getCfgNode() instanceof TupleNode
        or
        exists(Function func | func.getVararg().getAFlowNode() = this.getCfgNode())
    }

}

module TupleObject {

    TupleObject empty() {
        exists(Builtin empty |
            empty = result.asBuiltin() and
            empty.getClass() = theTupleType().asBuiltin() and 
            not exists(empty.getItem(_))
        )
    }

}

class NonEmptyTupleObject extends TupleObject {

    NonEmptyTupleObject() {
        exists(Function func | func.getVararg().getAFlowNode() = this.getCfgNode())
    }

}


class ListObject extends SequenceObject {

    ListObject() {
        this.asBuiltin().getClass() = theListType().asBuiltin()
        or
        this.getCfgNode() instanceof ListNode
    }

}

/** The `builtin` module */
BuiltinModuleObject theBuiltinModuleObject() {
    result.asBuiltin() = Builtin::builtinModule()
}

/** The `sys` module */
BuiltinModuleObject theSysModuleObject() {
    result.asBuiltin() = Builtin::special("sys")
}

/** DEPRECATED -- Use `Object::builtin(name)` instead. */
deprecated
Object builtin_object(string name) {
    result = Object::builtin(name)
}

/** The built-in object None */
Object theNoneObject() {
    result.asBuiltin() = Builtin::special("None")
}

/** The built-in object True */
Object theTrueObject() {
    result.asBuiltin() = Builtin::special("True")
}

/** The built-in object False */
Object theFalseObject() {
    result.asBuiltin() = Builtin::special("False")
}

/** The NameError class */
Object theNameErrorType() {
    result = Object::builtin("NameError")
}

/** The StandardError class */
Object theStandardErrorType() {
    result = Object::builtin("StandardError")
}

/** The IndexError class */
Object theIndexErrorType() {
    result = Object::builtin("IndexError")
}

/** The LookupError class */
Object theLookupErrorType() {
    result = Object::builtin("LookupError")
}

/** DEPRECATED -- Use `Object::quitter(name)` instead. */
deprecated
Object quitterObject(string name) {
    result = Object::quitter(name)
}

/** DEPRECATED -- Use `Object::notImplemented()` instead. */
deprecated
Object theNotImplementedObject() {
    result = Object::builtin("NotImplemented")
}

/** DEPRECATED -- Use `TupleObject::empty()` instead. */
deprecated
Object theEmptyTupleObject() {
    result = TupleObject::empty()
}

module Object {

    Object builtin(string name) {
        result.asBuiltin() = Builtin::builtin(name)
    }

    /** The named quitter object (quit or exit) in the builtin namespace */
    Object quitter(string name) {
        (name = "quit" or name = "exit") and
        result = builtin(name)
    }

    /** The builtin object `NotImplemented`. Not be confused with `NotImplementedError`. */
    Object notImplemented() {
        result = builtin("NotImplemented")
    }

}


/** Gets the pseudo-object representing an unknown value */
Object unknownValue() {
    result = TBuiltinObject(Builtin::unknown())
}


/** The builtin class 'list' */
ClassObject theListType() {
    result = TBuiltinObject(Builtin::special("list"))
}



private ClassObject comprehension(Expr e) {
    e instanceof ListComp and result = theListType()
    or
    e instanceof SetComp and result = theSetType()
    or
    e instanceof DictComp and result = theDictType()
    or
    e instanceof GeneratorExp and result = theGeneratorType()
}

private ClassObject collection_literal(Expr e) {
    e instanceof List and result = theListType()
    or
    e instanceof Set and result = theSetType()
    or
    e instanceof Dict and result = theDictType()
    or
    e instanceof Tuple and result = theTupleType()
}

private ClassObject string_literal(Expr e) {
    e instanceof Bytes and result = theBytesType()
    or
    e instanceof Unicode and result = theUnicodeType()
}

Object theUnknownType() {
    result.asBuiltin() = Builtin::special("_semmle_unknown_type")
}

