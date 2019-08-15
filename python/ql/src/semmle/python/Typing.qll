
private import semmle.python.objects.TObject as TObject
private import semmle.python.objects.ObjectAPI
import python as python
private import semmle.python.pointsto.PointsTo as PointsTo

class TypeHint extends TObject::TObject {

    TypeHint() {
        TypeHint::isType(this)
    }

    string toString() {
        result = this.typingModuleName()
        or
        not exists(this.typingModuleName()) and
        result = "class " + this.(ClassValue).getName()
    }

    private string typingModuleName() {
        this = Value::named(result) and result.prefix(7) = "typing."
    }

    /** Gets a (non-strict) super-type of this type.
     * NOTE: This is different from `ClassValue.getASuperType`
     * This should obey PEP 484 typing rules, not Python inheritance rules.
     */
    TypeHint getASuperType() {
        result = this.(ClassValue).getASuperType()
        // To do... many other cases
    }

    /** Gets a (non-strict) sub-type of this type. */
    TypeHint getASubType() {
        this = result.getASuperType()
    }

    /** Gets a string to identify this type. For use by taint-tracking. */
    string uuid() {
        /* This is incorrect, but should do for playing around */
        Value::named(result) = this
    }

}


class Optional extends TypeHint {

    Optional() {
        this = TObject::TSubscriptedType(TypeHint::optional(), _)
    }

    TypeHint getValue() {
        this = TObject::TSubscriptedType(_, result)
    }

    override TypeHint getASuperType() {
        result = Value::none_() or
        this = this.getValue().getASuperType()
    }

    override string toString() {
        result = "typing.Optional[" + this.getValue().toString() + "]"
    }
}

module TypeHint {

    predicate isType(Value v) {
         TObject::isType(v)
    }

    TypeHint fromClass(Value v) {
        result = v
    }

    TypeHint optional()  {
        result = Value::named("typing.Optional")
    }

    TypeHint forParameter(python::Parameter p) {
        p.getAnnotation().pointsTo(result)
        or
        p.getAnnotation().(python::StrConst).getText()
    }

    TypeHint forVariable(python::EssaVariable v) {
        v.getDefinition().(python::ParameterDefinition).getParameter().getAnnotation().pointsTo(result)
        or
        exists(python::AnnAssign asgn |
            v = v.getDefinition().(python::AssignmentDefinition).getVariable() and
            asgn.getAnnotation().pointsTo(result)
        )
    }

    class Generic extends TypeHint {

        Generic() {
            exists(string name |
                this = Value::named("typing." + name)
                |
                name = "List" or name = "Dict" or name = "Set" or
                name = "Counter" or name = "Deque" or name = "DefaultDict" or
                name = "FrozenSet"
            )
        }

    }

    class List extends Generic {

        List() {
            this = Value::named("typing.List")
        }
    }

    class Set extends Generic {

        Set() {
            this = Value::named("typing.Set")
        }
    }

    class Dict extends Generic {

        Dict() {
            this = Value::named("typing.Dict")
        }
    }

    class Specialised extends TypeHint {

        Specialised() {
            not this instanceof Optional and
            this = TObject::TSubscriptedType(_, _)
        }

        override string toString() {
            exists(Generic generic, TypeHint specific |
                this = TObject::TSubscriptedType(generic, specific) and
                result = generic.toString() + "[" + specific.toString() + "]"
            )
        }
    }

}


