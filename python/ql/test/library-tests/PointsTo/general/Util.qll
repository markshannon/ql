import python

string repr(Object o) {
    not o instanceof StringObject and not o = ClassObject::boundMethod() and result = o.toString()
    or
    /* Work around differing names in 2/3 */
    result = "'" + o.(StringObject).getText() + "'"
    or
    o = ClassObject::boundMethod() and result = "builtin-class method"
}
