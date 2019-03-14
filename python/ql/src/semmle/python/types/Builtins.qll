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
        py_cobjecttypes(this, result) and not this = Builtin::unknown()
        or
        this = Builtin::unknown() and result = Builtin::special("_semmle_unknown_type")
    }

    Builtin getMember(string name) {
        not name = ".super." and
        py_cmembers_versioned(this, name, result, major_version().toString())
    }

    predicate declaresMember(string name) {
        exists(Builtin val |
            val  = this.getMember(name) and
            not val = this.getBaseClass().getMember(name)
        )
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
        py_cobjecttypes(_, this) or this = Builtin::unknownType()
    }

    predicate isModule() {
        this.getClass() = Builtin::special("ModuleType")
    }

    predicate isStr() {
        this = Builtin::special("bytes") and major_version() = 2
        or
        this = Builtin::special("unicode") and major_version() = 3
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

    Builtin unknown() {
        py_special_objects(result, "_1")
    }
    
    Builtin unknownType() {
        py_special_objects(result, "_semmle_unknown_type")
    }
    
}