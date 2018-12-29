import python
private import semmle.python.pointsto.PointsTo
private import semmle.python.pointsto.Base
private import semmle.python.types.ModuleKind
private import semmle.python.types.Object


abstract class ModuleObject extends Object {

    /** Gets the scope corresponding to this module, if this is a Python module */
    abstract Module getModule();

    Container getPath() {
        none()
    }

    /** Gets the name of this scope */
    abstract string getName();

    override string toString() {
        result = "Module " + this.getName()
    }

    /** Gets the named attribute of this module. Using attributeRefersTo() instead
     * may provide better results for presentation. */
    pragma [noinline]
    abstract Object getAttribute(string name);

    /** Whether the named attribute of this module "refers-to" value, with a known origin.
     */
    abstract predicate attributeRefersTo(string name, Object value, Origin origin);

    /** Whether the named attribute of this module "refers-to" value, with known class and a known origin.
     */
    abstract predicate attributeRefersTo(string name, Object value, ClassObject cls, Origin origin);

    /** Gets the package for this module. */
    PackageObject getPackage() {
        this.getName().matches("%.%") and
        result.getName() = this.getName().regexpReplaceAll("\\.[^.]*$", "")
    }

    /** Whether the complete set of names "exported" by this module can be accurately determined */
    abstract predicate exportsComplete();

    /** Gets the short name of the module. For example the short name of module x.y.z is 'z' */
    string getShortName() {
        result = this.getName().suffix(this.getPackage().getName().length()+1)
        or
        result = this.getName() and not exists(this.getPackage())
    }

    /** Whether this module is imported by 'import name'. For example on a linux system,
      * the module 'posixpath' is imported as 'os.path' or as 'posixpath' */
    predicate importedAs(string name) {
        PointsTo::module_imported_as(this, name)
    }

    abstract predicate hasAttribute(string name);

    ModuleObject getAnImportedModule() {
        result.importedAs(this.getModule().getAnImportedModuleName())
    }

    /** Gets the kind for this module. Will be one of
     * "module", "script" or "plugin".
     */
    string getKind() {
        result = getKindForModule(this)
    }

    override boolean booleanValue() {
        result = true
    }

    override predicate maybe() { none() }

    override boolean isClass() {
        result = false
    }

}

class BuiltinModuleObject extends ModuleObject, BuiltinObject {

    BuiltinModuleObject() {
        py_cobjecttypes(this.getRaw(), theModuleType().getRaw())
    }

    override string toString() {
        result = ModuleObject.super.toString()
    }

    override string getName() {
        py_cobjectnames(this.getRaw(), result)
    }

    override Object getAttribute(string name) {
        py_cmembers_versioned(this.getRaw(), name, result.(BuiltinObject).getRaw(), major_version().toString())
    }

    override predicate hasAttribute(string name) {
        py_cmembers_versioned(this.getRaw(), name, _, major_version().toString())
    }

    override predicate attributeRefersTo(string name, Object value, Origin origin) {
        none() 
    }

    override predicate attributeRefersTo(string name, Object value, ClassObject cls, Origin origin) {
        none() 
    }

    override predicate exportsComplete() {
        any()
    }

    override Module getModule() {
        none()
    }

}

class PythonModuleObject extends ModuleObject, SourceObject {

    override string toString() {
        result = ModuleObject.super.toString()
    }

    PythonModuleObject() {
        exists(Module m | m.getEntryNode() = this.getFlowOrigin() |
            not m.isPackage()
        )
    }

    override string getName() {
        result = this.getModule().getName()
    }

    override Module getModule() {
        result = this.getOrigin()
    }

    override Container getPath() {
        result = this.getModule().getFile()
    }

    override Object getAttribute(string name) {
        this.attributeRefersTo(name, result, _, _)
    }

    override predicate exportsComplete() {
        exists(Module m |
            m = this.getModule() |
            not exists(Call modify, Attribute attr, GlobalVariable all | 
                modify.getScope() = m and modify.getFunc() = attr and 
                all.getId() = "__all__" |
                attr.getObject().(Name).uses(all)
            )
        )
    }

    override predicate hasAttribute(string name) {
        PointsTo::module_defines_name(this.getModule(), name)
        or
        this.attributeRefersTo(name, _, _, _)
        or
        /* The interpreter always adds the __name__ and __package__ attributes */
        name = "__name__" or name = "__package__"
    }

    override predicate attributeRefersTo(string name, Object value, Origin origin) {
         PointsTo::py_module_attributes(this.getModule(), name, value, _, origin)
    }

    override predicate attributeRefersTo(string name, Object value, ClassObject cls, Origin origin) {
         PointsTo::py_module_attributes(this.getModule(), name, value, cls, origin)
    }

    override ClassObject getAnInferredType() {
        result = theModuleType()
    }

    override boolean isComparable() {
        result = true
    }
    
}

/**  Primarily for internal use.
 *
 * Gets the object for the string text. 
 * The extractor will have populated a str object 
 * for each module name, with the name b'text' or u'text' (including the quotes).
 */
BuiltinObject object_for_string(string text) {
    py_cobjecttypes(result.getRaw(), theStrType().getRaw()) and
    exists(string repr |
        py_cobjectnames(result.getRaw(), repr) and
        repr.charAt(1) = "'" |
        /* Strip quotes off repr */
        text = repr.substring(2, repr.length()-1)
    )
}
