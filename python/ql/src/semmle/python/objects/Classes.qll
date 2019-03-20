import python


private import semmle.python.objects.TObject
private import semmle.python.objects.ObjectInternal
private import semmle.python.pointsto.PointsTo2
private import semmle.python.pointsto.PointsToContext2
private import semmle.python.pointsto.MRO2
private import semmle.python.types.Builtins


abstract class ClassObjectInternal extends ObjectInternal {

    override boolean booleanValue() {
        result = true
    }

    override predicate maybe() { none() }

    override predicate isClass() { any() }

    override predicate notClass() { none() }

    override int intValue() {
        none()
    }

    override string strValue() {
        none()
    }

    string getName() {
        result = this.getClassDeclaration().getName()
    }

    abstract predicate attribute(string name, ObjectInternal value, CfgOrigin origin);

    boolean isSpecial() {
        result = Types::getMro(this).isSpecial()
    }
}

class PythonClassObjectInternal extends ClassObjectInternal, TPythonClassObject {

    Class getScope() {
        exists(ClassExpr expr |
            this = TPythonClassObject(expr.getAFlowNode()) and
            result = expr.getInnerScope()
        )
    }

    override string toString() {
        result = "class " + this.getScope().getName()
    }

    override predicate introduced(ControlFlowNode node, PointsToContext2 context) {
        this = TPythonClassObject(node) and context.appliesTo(node)
    }

    override ClassDecl getClassDeclaration() {
        this = TPythonClassObject(result)
    }

    override ObjectInternal getClass() {
        result = Types::getMetaClass(this)
    }

    override Builtin getBuiltin() {
        none()
    }

    override ControlFlowNode getOrigin() {
        this = TPythonClassObject(result)
    }

    override predicate calleeAndOffset(Function scope, int paramOffset) {
        exists(PythonFunctionObjectInternal init |
            // TO DO... Lookup init...
            none() |
            init.getScope() = scope and paramOffset = 1
        )
    }

    override predicate attribute(string name, ObjectInternal value, CfgOrigin origin) {
        exists(ClassObjectInternal decl |
            decl = Types::getMro(this).findDeclaringClass(name) |
            Types::declaredAttribute(decl, name, value, origin)
        )
    }

    override predicate callResult(PointsToContext2 callee, ObjectInternal obj, CfgOrigin origin) {
        // TO DO .. Result should (in most cases) be an instance
        none()
    }

    override predicate isComparable() {
        any()
    }

    override predicate notComparable() {
        none()
    }

}

class BuiltinClassObjectInternal extends ClassObjectInternal, TBuiltinClassObject {

    override Builtin getBuiltin() {
        this = TBuiltinClassObject(result)
    }

    override string toString() {
        result = "builtin class " + this.getBuiltin().getName()
    }

    override predicate introduced(ControlFlowNode node, PointsToContext2 context) {
        none()
    }

    override ClassDecl getClassDeclaration() {
        this = TBuiltinClassObject(result)
    }

    override ObjectInternal getClass() {
        result = TBuiltinClassObject(this.getBuiltin().getClass())
    }

    override ControlFlowNode getOrigin() {
        none()
    }

    override predicate calleeAndOffset(Function scope, int paramOffset) {
        none()
    }

    override predicate attribute(string name, ObjectInternal value, CfgOrigin origin) {
        value.getBuiltin() = this.getBuiltin().getMember(name) and origin = CfgOrigin::unknown()
    }

    override predicate callResult(PointsToContext2 callee, ObjectInternal obj, CfgOrigin origin) {
        // TO DO .. Result should (in most cases) be an instance
        none()
    }

    override predicate isComparable() {
        any()
    }

    override predicate notComparable() {
        none()
    }

}


class UnknownClassInternal extends ClassObjectInternal, TUnknownClass {

    override string toString() {
        none()
    }

    override ClassDecl getClassDeclaration() {
        result = Builtin::unknownType()
    }

    override ObjectInternal getClass() {
        result = TUnknownClass()
    }

    override predicate introduced(ControlFlowNode node, PointsToContext2 context) {
        none()
    }

    override predicate isComparable() {
        none()
    }

    override predicate notComparable() {
        any()
    }

    override Builtin getBuiltin() {
        none()
    }

    override predicate callResult(PointsToContext2 callee, ObjectInternal obj, CfgOrigin origin) {
        obj = ObjectInternal::unknown() and origin = CfgOrigin::unknown() and
        callee_for_object(callee, this)
    }

    override ControlFlowNode getOrigin() {
        none()
    }

    override predicate calleeAndOffset(Function scope, int paramOffset) {
        none()
    }

    override predicate attribute(string name, ObjectInternal value, CfgOrigin origin) {
        none()
    }

}

