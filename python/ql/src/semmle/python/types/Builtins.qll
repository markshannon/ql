import python

class Builtin extends @py_cobject {

    Builtin() {
        not (
            /* @py_cobjects for modules which have a corresponding Python module */
            exists(@py_cobject mod_type | py_special_objects(mod_type, "ModuleType") and py_cobjecttypes(this, mod_type)) and
            exists(Module m | py_cobjectnames(this, m.getName()))
        )
        and (
            /* Exclude unmatched builtin objects in the library trap files */
            py_cobjectnames(this, _) or
            py_cobjecttypes(this, _) or
            py_special_objects(this, _)
        )
    }

    string toString() {
        not this = undefinedVariable().asBuiltin() and not this = unknownValue().asBuiltin() and
        exists(Builtin type, string typename, string objname |
            py_cobjecttypes(this, type) and py_cobjectnames(this, objname) and typename = type.getName() |
            result = typename + " " + objname
        )
    }

    Builtin getClass() {
        py_cobjecttypes(this, result) and not this = unknownValue().asBuiltin()
        or
        this = unknownValue().asBuiltin() and result = theUnknownType().asBuiltin()
    }

    Builtin getMember(string name) {
        not name = ".super." and
        py_cmembers_versioned(this, name, result, major_version().toString())
    }

    Builtin getItem(int index) {
        py_citems(this, index, result)
    }

    Builtin getBaseClass() {
        py_cmembers_versioned(this, ".super.", result, major_version().toString())
    }

    predicate inheritsFromType() {
        this = Builtin::special("type")
        or
        this.getBaseClass().inheritsFromType()
    }

    string getName() {
        py_cobjectnames(this, result)
    }

    predicate isClass() {
        py_cobjecttypes(_, this) or this = theUnknownType().asBuiltin()
    }

}

module Builtin {

    Builtin builtinModule() {
        py_special_objects(result, "builtin_module_2") and major_version() = 2
        or
        py_special_objects(result, "builtin_module_3") and major_version() = 3
    }

    Builtin builtin(string name) {
        result = builtinModule().getMember(name)
    }

    Builtin special(string name) {
        py_special_objects(result, name)
    }

}