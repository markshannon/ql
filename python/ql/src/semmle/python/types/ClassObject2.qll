import python
import semmle.python.types.Object2

abstract class ClassObject2 extends Object2 {

    /** Gets the short (unqualified) name of this class */
    abstract string getName();

    /** Gets the qualified name for this class.
     * Should return the same name as the `__qualname__` attribute on classes in Python 3.
     */
    abstract string getQualifiedName();

    /** Gets the scope associated with this class, if it is not a builtin class */
    Class getPyClass() { none() }

}

class BuiltinClassObject extends ClassObject2, BuiltinObject2 {

    BuiltinClassObject() {
        exists(Object meta | py_cobjecttypes(this.getRaw(), meta) and is_c_metaclass(meta))
    }

    private predicate isStr() {
        py_special_objects(this.getRaw(), "bytes") and major_version() = 2
        or
        py_special_objects(this.getRaw(), "unicode") and major_version() = 3
    }

    override string getName() {
        this.isStr() and result = "str"
        or
        not this.isStr() and py_cobjectnames(this.getRaw(), result)
    }

    override string getQualifiedName() {
        py_cobjectnames(this.getRaw(), _) and result = this.getName()
        or
        result = this.getPyClass().getQualifiedName()
    }

}

class SourceClassObject extends ClassObject2, SourceObject {

    SourceClassObject() {
        this.getOrigin() instanceof ClassExpr
    }

    override Class getPyClass() {
        result.getParent().getAFlowNode() = this.getFlowOrigin()
    }

    override string getName() {
        result = this.getPyClass().getName()
    }

    override string getQualifiedName() {
        result = this.getPyClass().getQualifiedName()
    }

}

