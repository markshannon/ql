import python

module Exceptions {

    /** The builtin class `BaseException` */
    ClassObject baseException() {
        py_special_objects(result, "BaseException")
    }

    /** The builtin class `Exception` */
    ClassObject exception() {
        py_special_objects(result, "Exception")
    }

    /** The builtin class `TypeError` */
    ClassObject typeError() {
        py_special_objects(result, "TypeError")
    }

    /** The builtin class `AttributeError` */
    ClassObject attributeError() {
        py_special_objects(result, "AttributeError")
    }

    /** The builtin class `KeyError` */
    ClassObject keyError() {
        py_special_objects(result, "KeyError")
    }

    /** The builtin class `IOError` */
    ClassObject ioError() {
        result = Object::builtin("IOError")
    }

    /** The builtin class `NotImplementedError` */
    ClassObject notImplementedError() {
        result = Object::builtin("NotImplementedError")
    }

}