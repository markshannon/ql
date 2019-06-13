/**
 * @name Conflicting attributes in base classes
 * @description When a class subclasses multiple base classes and more than one base class defines the same attribute, attribute overriding may result in unexpected behavior by instances of this class.
 * @kind problem
 * @tags reliability
 *       maintainability
 *       modularity
 * @problem.severity warning
 * @sub-severity low
 * @precision high
 * @id py/conflicting-attributes
 */

import python

predicate does_nothing(CallableValue f) {
    not exists(Stmt s | s.getScope() = f.getScope() |
        not s instanceof Pass and not ((ExprStmt)s).getValue() = f.getScope().getDocString()
    )
}

/* If a method performs a super() call then it is OK as the 'overridden' method will get called */
predicate calls_super(CallableValue f) {
    exists(Call sup, Call meth, Attribute attr, GlobalVariable v | 
        meth.getScope() = f.getScope() and
        meth.getFunc() = attr and
        attr.getObject() = sup and
        attr.getName() = f.getName() and
        sup.getFunc() = v.getAnAccess() and
        v.getId() = "super"
    )
}

/** Holds if the given name is white-listed for some reason */
predicate whitelisted(string name) {
    /* The standard library specifically recommends this :(
     * See https://docs.python.org/3/library/socketserver.html#asynchronous-mixins */
    name = "process_request"
}


from ClassValue c, ClassValue b1, ClassValue b2, string name,
int i1, int i2, Value o1, Value o2
where c.getBaseType(i1) = b1 and
c.getBaseType(i2) = b2 and 
i1 < i2 and o1 != o2 and
o1 = b1.lookup(name) and 
o2 = b2.lookup(name) and
not name.matches("\\_\\_%\\_\\_") and
not calls_super(o1) and
not does_nothing(o2) and
not whitelisted(name) and
not o1.overrides(o2) and
not o2.overrides(o1) and
not c.declares(name)

select c, "Base classes have conflicting values for attribute '" + name + "': $@ and $@.", o1, o1.toString(), o2, o2.toString()

