import python
import semmle.python.types.Object

abstract class ModuleObject extends Object {


    /** Gets the scope corresponding to this module, if this is a Python module */
    Module getModule() {
        none()
    }

    Container getPath() {
        none()
    }

    /** Gets the name of this scope */
    abstract string getName();

    override string toString() {
        result = "Module " + this.getName()
    }

}

class BuiltinModuleObject extends ModuleObject, BuiltinObject {

    BuiltinModuleObject() {
        py_cobjecttypes(this.getRaw(), theModuleType())
    }

    override string toString() {
        result = ModuleObject.super.toString()
    }

    override string getName() {
        py_cobjectnames(this.getRaw(), result)
    }

}


class PythonModuleObject extends ModuleObject, SourceObject {

    override string toString() {
        result = ModuleObject.super.toString()
    }

    override string getName() {
        result = this.getModule().getName()
    }

    override Module getModule() {
        result = this.getOrigin()
    }

}

