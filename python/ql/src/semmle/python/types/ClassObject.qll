import python
private import semmle.python.pointsto.PointsTo
private import semmle.python.pointsto.Base
private import semmle.python.pointsto.MRO as MRO

predicate is_c_metaclass(@py_cobject o) {
    py_special_objects(o, "type")
    or
    exists(@py_cobject sup | py_cmembers_versioned(o, ".super.", sup, major_version().toString()) and is_c_metaclass(sup))
}


private newtype TOrigin =
    SourceOrigin(ControlFlowNode n)
    or
    UnknownOrigin()

library class Origin extends TOrigin {

    string toString() {
        /* Not to be displayed */
        none()
    }

    /** Potentially lossy conversion from `Origin` to `ControlFlowNode`
     * Will produce no result if this is unknown.
     */
    ControlFlowNode asFlowNode() {
        SourceOrigin(result) = this
    }

    pragma[inline]
    ControlFlowNode asFlowNode(ControlFlowNode here) {
        SourceOrigin(result) = this
        or
        this = UnknownOrigin() and result = here
    }

}

deprecated class ObjectOrCfg = Origin;

module Origin {

    Origin unknown() {
        result = UnknownOrigin()
    }

}

/** A class whose instances represents Python classes.
 *  Instances of this class represent either builtin classes 
 *  such as `list` or `str`, or program-defined Python classes 
 *  present in the source code.
 *  
 *  Generally there is a one-to-one mapping between classes in 
 *  the Python program and instances of this class in the database. 
 *  However, that is not always the case. For example, dynamically 
 *  generated classes may share a single QL class instance.
 *  Also the existence of a class definition in the source code 
 *  does not guarantee that such a class will ever exist in the 
 *  running program.
 */
abstract class ClassObject extends Object {

    /** Gets the short (unqualified) name of this class */
    abstract string getName();

    /** Gets the qualified name for this class.
     * Should return the same name as the `__qualname__` attribute on classes in Python 3.
     */
    abstract string getQualifiedName();

    /** Gets the nth base class of this class */
    Object getBaseType(int n) {
        result = PointsTo::Types::class_base_type(this, n)
    }

    /** Gets a base class of this class */
    Object getABaseType() {
        result = this.getBaseType(_)
    }

    /** Whether this class has a base class */
    predicate hasABase() {
        exists(ClassExpr cls | this.(SourceObject).getOrigin() = cls | exists(cls.getABase()))
        or
        /* The extractor uses the special name ".super." to indicate the super class of a builtin class */
        py_cmembers_versioned(this.(BuiltinClassObject).getRaw(), ".super.", _, major_version().toString())
    }

    /** Gets a super class of this class (includes transitive super classes) */
    ClassObject getASuperType() {
        result = PointsTo::Types::get_a_super_type(this)
    }

    /** Gets a super class of this class (includes transitive super classes) or this class */
    ClassObject getAnImproperSuperType() {
        result = PointsTo::Types::get_an_improper_super_type(this)
    }

    /** Whether this class is a new style class. 
        A new style class is one that implicitly or explicitly inherits from `object`. */
    predicate isNewStyle() {
        PointsTo::Types::is_new_style(this)
    }

    /** Whether this class is a legal exception class. 
     *  What constitutes a legal exception class differs between major versions */
    predicate isLegalExceptionType() {
        not this.isNewStyle() or
        this.getAnImproperSuperType() = theBaseExceptionType()
        or
        major_version() = 2 and this = theTupleType()
    }

    /** Gets the scope associated with this class, if it is not a builtin class */
    Class getPyClass() {
        result.getClassObject() = this
    }

    /** Returns an attribute declared on this class (not on a super-class) */
    Object declaredAttribute(string name) {
        PointsTo::Types::class_declared_attribute(this, name, result, _, _)
    }

    /** Returns an attribute declared on this class (not on a super-class) */
    predicate declaresAttribute(string name) {
        class_declares_attribute(this, name)
    }

    /** Returns an attribute declared on this class (not on a super-class) */
    abstract boolean declaresAttributeBoolean(string name);

    /** Returns an attribute as it would be when looked up at runtime on this class.
      Will include attributes of super-classes */
    Object lookupAttribute(string name) {
        result = this.getMro().lookup(name)
    }

    MRO::ClassList getMro() {
        PointsTo::Types::is_new_style_bool(this) = true and
        result = MRO::new_style_mro(this)
        or
        result = MRO::old_style_mro(this)
    }

    /** Looks up an attribute by searching this class' MRO starting at `start` */
    Object lookupMro(ClassObject start, string name) {
        result = this.getMro().startingAt(start).lookup(name)
    }

    /** Whether the named attribute refers to the object and origin */
    predicate attributeRefersTo(string name, Object obj, Origin origin) {
        PointsTo::Types::class_attribute_lookup(this, name, obj, _, origin)
    }

    /** Whether the named attribute refers to the object, class and origin */
    predicate attributeRefersTo(string name, Object obj, ClassObject cls, Origin origin) {
        not obj = unknownValue() and
        PointsTo::Types::class_attribute_lookup(this, name, obj, cls, origin)
    }

    /** Whether this class has a attribute named `name`, either declared or inherited.*/
    predicate hasAttribute(string name) {
        PointsTo::Types::class_has_attribute(this, name)
    }

    /** Whether it is impossible to know all the attributes of this class. Usually because it is
        impossible to calculate the full class hierarchy or because some attribute is too dynamic. */
    predicate unknowableAttributes() {
        /* True for a class with undeterminable superclasses, unanalysable metaclasses, or other confusions */
        this.failedInference()
        or
        this.getMetaClass().failedInference()
        or
        exists(Object base |
            base = this.getABaseType() |
            base.(ClassObject).unknowableAttributes()
            or
            not base instanceof ClassObject
        )
    }

    /** Gets the metaclass for this class */
    ClassObject getMetaClass() {
        result = PointsTo::Types::class_get_meta_class(this)
        and
        not this.failedInference()
    }

    /* Whether this class is abstract. */
    predicate isAbstract() {
        this.getMetaClass() = theAbcMetaClassObject()
        or
        exists(FunctionObject f, Raise r, Name ex |
            f = this.lookupAttribute(_) and
            r.getScope() = f.getFunction() |
            (r.getException() = ex or r.getException().(Call).getFunc() = ex) and
            (ex.getId() = "NotImplementedError" or ex.getId() = "NotImplemented")
        )
    }

    ControlFlowNode declaredMetaClass() {
        result = this.getPyClass().getMetaClass().getAFlowNode()
    }

    /** Has type inference failed to compute the full class hierarchy for this class for the reason given. */ 
    predicate failedInference(string reason) {
        PointsTo::Types::failed_inference(this, reason)
    }

    /** Has type inference failed to compute the full class hierarchy for this class */ 
    predicate failedInference() {
        this.failedInference(_)
    }

    /** Gets an object which is the sole instance of this class, if this class is probably a singleton.
     *  Note the 'probable' in the name; there is no guarantee that this class is in fact a singleton.
     *  It is guaranteed that getProbableSingletonInstance() returns at most one Object for each ClassObject. */
    Object getProbableSingletonInstance() {
        exists(ControlFlowNode use, Expr origin |
            use.refersTo(result, this, origin.getAFlowNode())
            |
            this.hasStaticallyUniqueInstance()
            and
            /* Ensure that original expression will be executed only one. */
            origin.getScope() instanceof ImportTimeScope and
            not exists(Expr outer | outer.getASubExpression+() = origin)
        )
        or
        this = theNoneType() and result = theNoneObject()
    }

    /** This class is only instantiated at one place in the code */
    private  predicate hasStaticallyUniqueInstance() {
        strictcount(Object instances | PointsTo::points_to(_, _, instances, this, _)) = 1
    }

    ImportTimeScope getImportTimeScope() {
        result = this.getPyClass()
    }

    /* Method Resolution Order */

    /** Returns the next class in the MRO of 'this' after 'sup' */
    ClassObject nextInMro(ClassObject sup) {
        exists(MRO::ClassList mro, int i |
            mro = this.getMro() and
            sup = mro.getItem(i) and
            result = mro.getItem(i+1)
        ) and
        not this.failedInference()
    }

    /** Gets the MRO for this class. ClassObject `sup` occurs at `index` in the list of classes.
     * `this` has an index of `1`, the next class in the MRO has an index of `2`, and so on.
     */
    ClassObject getMroItem(int index) {
        result = this.getMro().getItem(index)
    }

    /** Holds if this class has duplicate base classes */
    predicate hasDuplicateBases() {
        exists(ClassObject base, int i, int j | i != j and base = this.getBaseType(i) and base = this.getBaseType(j))
    }

    /** Holds if this class is an iterable. */
    predicate isIterable() {
        this.hasAttribute("__iter__") or this.hasAttribute("__getitem__")
    }

    /** Holds if this class is an iterator. */
    predicate isIterator() {
        this.hasAttribute("__iter__") and 
        (major_version() = 3 and this.hasAttribute("__next__")
         or   
         /* Because 'next' is a common method name we need to check that an __iter__
          * method actually returns this class. This is not needed for Py3 as the
          * '__next__' method exists to define a class as an iterator.
          */
         major_version() = 2 and this.hasAttribute("next") and 
         exists(ClassObject other, FunctionObject iter | 
            other.declaredAttribute("__iter__") = iter |
            iter.getAnInferredReturnType() = this
         )
        )
        or
        /* This will be redundant when we have C class information */
        this = theGeneratorType()
    }

    /** Holds if this class is an improper subclass of the other class.
     *  True if this is a sub-class of other or this is the same class as other.
     *
     *  Equivalent to the Python builtin function issubclass().
     */
    predicate isSubclassOf(ClassObject other) {
        this = other or this.getASuperType() = other
    }

    /** Synonymous with isContainer(), retained for backwards compatibility. */
    predicate isCollection() {
        this.isContainer()
    }

    /** Holds if this class is a container(). That is, does it have a __getitem__ method.*/
    predicate isContainer() {
        exists(this.lookupAttribute("__getitem__"))
    }

    /** Holds if this class is a mapping. */
    predicate isMapping() {
        exists(this.lookupAttribute("__getitem__"))
        and
        not this.isSequence()
    }

    /** Holds if this class is probably a sequence. */
    predicate isSequence() {
        /* To determine whether something is a sequence or a mapping is not entirely clear,
         * so we need to guess a bit. 
         */
        this.getAnImproperSuperType() = theTupleType()
        or
        this.getAnImproperSuperType() = theListType()
        or
        this.getAnImproperSuperType() = theRangeType()
        or
        this.getAnImproperSuperType() = theBytesType()
        or
        this.getAnImproperSuperType() = theUnicodeType()
        or
        /* Does this inherit from abc.Sequence? */
        this.getASuperType().getName() = "Sequence"
        or
        /* Does it have an index or __reversed__ method? */
        this.isContainer() and
        (
            this.hasAttribute("index") or 
            this.hasAttribute("__reversed__")
        )
    }

    predicate isCallable() {
        this.hasAttribute("__call__")
    }

    predicate isContextManager() {
        this.hasAttribute("__enter__") and this.hasAttribute("__exit__")
    }

    predicate assignedInInit(string name) {
        exists(FunctionObject init | init = this.lookupAttribute("__init__") |
            attribute_assigned_in_method(init, name)
        )
    }

    /** Holds if this class is unhashable */
    predicate unhashable() {
        this.lookupAttribute("__hash__") = theNoneObject()
        or
        ((FunctionObject)this.lookupAttribute("__hash__")).neverReturns() 
    }

    /** Holds if this class is a descriptor */
    predicate isDescriptorType() {
        this.hasAttribute("__get__") 
    }

    /** Holds if this class is an overriding descriptor */
    predicate isOverridingDescriptorType() {
        this.hasAttribute("__get__") and this.hasAttribute("__set__") 
    }

    FunctionObject getAMethodCalledFromInit() {
        exists(FunctionObject init |
            init = this.lookupAttribute("__init__") and
            init.getACallee*() = result
        )
    }

    override boolean booleanValue() {
        result = true
    }

    /** Gets a call to this class. Note that the call may not create a new instance of
     * this class, as that depends on the `__new__` method of this class.
     */
    CallNode getACall() {
        result.getFunction().refersTo(this)
    }

    override boolean isClass() { result = true }

}

private predicate isStr(@py_cobject raw) {
    py_special_objects(raw, "bytes") and major_version() = 2
    or
    py_special_objects(raw, "unicode") and major_version() = 3
}

class BuiltinClassObject extends ClassObject, BuiltinObject {

    BuiltinClassObject() {
        exists(@py_cobject raw |
            this.(BuiltinObject).getRaw() = raw |
            py_cobjecttypes(_, raw) or
            exists(@py_cobject meta | py_cobjecttypes(raw, meta) and is_c_metaclass(meta))
        )
    }

    override string getName() {
        exists(@py_cobject raw |
            this.(BuiltinObject).getRaw() = raw |
            if isStr(raw) then
                result = "str"
            else
                py_cobjectnames(raw, result)
        )
    }

    override string toString() {
        result = "class " + this.getName()
    }

    override predicate maybe() { none() }

    override string getQualifiedName() {
        py_cobjectnames(this.getRaw(), _) and result = this.getName()
    }

    override boolean declaresAttributeBoolean(string name) {
        relevant_to_class_declares_names(this, name) and
        exists(@py_cobject raw | raw = this.getRaw()
            |
            if builtin_class_defines_name(raw, name) then
                result = true
            else
                result = false
        )
    }


}

class SourceClassObject extends ClassObject, SourceObject {

    SourceClassObject() {
        this.getOrigin() instanceof ClassExpr
    }

    override ClassObject getAnInferredType() {
        result = PointsTo::Types::class_get_meta_class(this)
    }

    override string getName() {
        result = this.getPyClass().getName()
    }

    override string toString() {
        result = "builtin-class " + this.getName()
    }

    override predicate maybe() { none() }

    override string getQualifiedName() {
        result = this.getPyClass().getQualifiedName()
    }

    override boolean isComparable() {
        result = true
    }

    override boolean declaresAttributeBoolean(string name) {
        relevant_to_class_declares_names(this, name) and
        exists(Class cls |
            cls = this.getPyClass()
            |
            if class_defines_name(cls, name) then
                result = true
            else
                result = false
        )
    }

}

/** Holds if the class defines name */
private predicate class_defines_name(Class cls, string name) {
    exists(SsaVariable var | name = var.getId() and var.getAUse() = cls.getANormalExit())
}

/** The 'str' class. This is the same as the 'bytes' class for
  * Python 2 and the 'unicode' class for Python 3 */
BuiltinClassObject theStrType() {
    if major_version() = 2 then
        result = theBytesType()
    else
        result = theUnicodeType()
}

private
Module theAbcModule() {
    result.getName() = "abc"
}

ClassObject theAbcMetaClassObject() {
    /* Avoid using points-to and thus negative recursion */
    exists(Class abcmeta |
        result.getPyClass() = abcmeta |
        abcmeta.getName() = "ABCMeta" and
        abcmeta.getScope() = theAbcModule()
    )
}

/* Common builtin classes */

/** The built-in class NoneType*/
BuiltinClassObject theNoneType() {
    py_special_objects(result.getRaw(), "NoneType")
}

/** The built-in class 'bool' */
BuiltinClassObject theBoolType() {
    py_special_objects(result.getRaw(), "bool")
}

/** The builtin class 'type' */
BuiltinClassObject theTypeType() {
    py_special_objects(result.getRaw(), "type")
}

/** The builtin object ClassType (for old-style classes) */
BuiltinClassObject theClassType() {
    py_special_objects(result.getRaw(), "ClassType")
}

/** The builtin object InstanceType (for old-style classes) */
BuiltinClassObject theInstanceType() {
    py_special_objects(result.getRaw(), "InstanceType")
}

/** The builtin class 'tuple' */
BuiltinClassObject theTupleType() {
    py_special_objects(result.getRaw(), "tuple")
}

/** The builtin class 'int' */
BuiltinClassObject theIntType() {
    py_special_objects(result.getRaw(), "int")
}

/** The builtin class 'long' (Python 2 only) */
BuiltinClassObject theLongType() {
    py_special_objects(result.getRaw(), "long")
}

/** The builtin class 'float' */
BuiltinClassObject theFloatType() {
    py_special_objects(result.getRaw(), "float")
}

/** The builtin class 'complex' */
BuiltinClassObject theComplexType() {
    py_special_objects(result.getRaw(), "complex")
}

/** The builtin class 'object' */
BuiltinClassObject theObjectType() {
    py_special_objects(result.getRaw(), "object")
}

/** The builtin class 'list' */
BuiltinClassObject theListType() {
    py_special_objects(result.getRaw(), "list")
}

@py_cobject rawListType() {
    py_special_objects(result, "list")
}

/** The builtin class 'dict' */
BuiltinClassObject theDictType() {
    py_special_objects(result.getRaw(), "dict")
}

@py_cobject rawDictType() {
    py_special_objects(result, "dict")
}

/** The builtin class 'Exception' */

BuiltinClassObject theExceptionType() {
    py_special_objects(result.getRaw(), "Exception")
}

/** The builtin class for unicode. unicode in Python2, str in Python3 */
BuiltinClassObject theUnicodeType() {
    py_special_objects(result.getRaw(), "unicode")
}

/** The builtin class '(x)range' */
BuiltinClassObject theRangeType() {
    result = builtin_object("xrange")
    or
    major_version() = 3 and result = builtin_object("range")
}

/** The builtin class for bytes. str in Python2, bytes in Python3 */
BuiltinClassObject theBytesType() {
    py_special_objects(result.getRaw(), "bytes")
}

/** The builtin class 'set' */
BuiltinClassObject theSetType() {
    py_special_objects(result.getRaw(), "set")
}

@py_cobject rawSetType() {
    py_special_objects(result, "set")
}

/** The builtin class 'property' */
BuiltinClassObject thePropertyType() {
    py_special_objects(result.getRaw(), "property")
}

/** The builtin class 'BaseException' */
BuiltinClassObject theBaseExceptionType() {
    py_special_objects(result.getRaw(), "BaseException")
}

/** The class of builtin-functions */
BuiltinClassObject theBuiltinFunctionType() {
    py_special_objects(result.getRaw(), "BuiltinFunctionType")
}

/** The class of Python functions */
BuiltinClassObject thePyFunctionType() {
    py_special_objects(result.getRaw(), "FunctionType")
}

/** The builtin class 'classmethod' */
BuiltinClassObject theClassMethodType() {
    py_special_objects(result.getRaw(), "ClassMethod")
}

/** The builtin class 'staticmethod' */
BuiltinClassObject theStaticMethodType() {
    py_special_objects(result.getRaw(), "StaticMethod")
}

/** The class of modules */
BuiltinClassObject theModuleType() {
    py_special_objects(result.getRaw(), "ModuleType")
}

/** The class of modules */
@py_cobject rawModuleType() {
    py_special_objects(result, "ModuleType")
}

/** The class of generators */
BuiltinClassObject theGeneratorType() {
    py_special_objects(result.getRaw(), "generator")
}

/** The builtin class 'TypeError' */
BuiltinClassObject theTypeErrorType() {
    py_special_objects(result.getRaw(), "TypeError")
}

/** The builtin class 'AttributeError' */
BuiltinClassObject theAttributeErrorType() {
    py_special_objects(result.getRaw(), "AttributeError")
}

/** The builtin class 'KeyError' */
BuiltinClassObject theKeyErrorType() {
    py_special_objects(result.getRaw(), "KeyError")
}

/** The builtin class of bound methods */
pragma [noinline]
BuiltinClassObject theBoundMethodType() {
    py_special_objects(result.getRaw(), "MethodType")
}

/** The builtin class of builtin properties */
BuiltinClassObject theGetSetDescriptorType() {
     py_special_objects(result.getRaw(), "GetSetDescriptorType")
}

/** The method descriptor class */
BuiltinClassObject theMethodDescriptorType() {
    py_special_objects(result.getRaw(), "MethodDescriptorType")
}

/** The class of builtin properties */
ClassObject theBuiltinPropertyType() {
    /* This is CPython specific */
    result = theGetSetDescriptorType()
}

/** The builtin class 'IOError' */
ClassObject theIOErrorType() {
    result = builtin_object("IOError")
}

/** The builtin class 'super' */
ClassObject theSuperType() {
    result = builtin_object("super")
}

/** The builtin class 'StopIteration' */
ClassObject theStopIterationType() {
    result = builtin_object("StopIteration")
}

/** The builtin class 'NotImplementedError' */
ClassObject theNotImplementedErrorType() {
    result = builtin_object("NotImplementedError")
}



private predicate relevant_to_class_declares_names(ClassObject cls, string name) {
    exists(MRO::ClassList mro |
        any(ClassObject c).getMro() = mro and
        mro.getAnItem() = cls and
        mro.getAnItem().declaresAttribute(name)
    )
    or
    PointsTo::Types::interesting_attribute(cls, name)
}
