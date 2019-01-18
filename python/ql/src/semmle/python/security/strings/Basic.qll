import python
private import Common

import semmle.python.security.TaintTracking

/** An extensible kind of taint representing any kind of string.
 */
abstract class StringKind extends TaintKind {

    bindingset[this]
    StringKind() {
        this = this
    }

    override TaintKind getTaintForFlowStep(ControlFlowNode fromnode, ControlFlowNode tonode) {
        result = this and
        (
            str_method_call(fromnode, tonode) or
            slice(fromnode, tonode) or
            tonode.(BinaryExprNode).getAnOperand() = fromnode or
            os_path_join(fromnode, tonode) or
            str_format(fromnode, tonode) or
            encode_decode(fromnode, tonode) or
            to_str(fromnode, tonode)
        )
        or
        result = this and copy_call(fromnode, tonode)
    }

    override ClassObject getClass() {
        result = theStrType() or result = ClassObject::unicode()
    }

}

private class StringEqualitySanitizer extends Sanitizer {

    StringEqualitySanitizer() { this = "string equality sanitizer" }

    /** The test `if untrusted == "KNOWN_VALUE":` sanitizes `untrusted` on its `true` edge. */
    override predicate sanitizingEdge(TaintKind taint, PyEdgeRefinement test) {
        taint instanceof StringKind and
        exists(ControlFlowNode const, Cmpop op |
            const.getNode() instanceof StrConst |
            (
                test.getTest().(CompareNode).operands(const, op, _)
                or
                test.getTest().(CompareNode).operands(_, op, const)
            ) and (
                op instanceof Eq and test.getSense() = true
                or
                op instanceof NotEq and test.getSense() = false
            )
        )
    }

}

/* tonode = fromnode.xxx() where the call to xxx returns an identical or similar string */
private predicate str_method_call(ControlFlowNode fromnode, CallNode tonode) {
    exists(string method_name |
        tonode.getFunction().(AttrNode).getObject(method_name) = fromnode
        |
        method_name = "strip" or method_name = "format" or
        method_name = "lstrip" or method_name = "rstrip" or
        method_name = "ljust" or method_name = "rjust" or
        method_name = "title" or method_name = "capitalize"
    )
}

/* tonode = ....format(fromnode) */
private predicate str_format(ControlFlowNode fromnode, CallNode tonode) {
    tonode.getFunction().(AttrNode).getName() = "format" and
    (
        tonode.getAnArg() = fromnode
        or
        tonode.getNode().getAKeyword().getValue() = fromnode.getNode()
    )
}

/* tonode = codec.[en|de]code(fromnode)*/
private predicate encode_decode(ControlFlowNode fromnode, CallNode tonode) {
    exists(FunctionObject func, string name |
        func.getACall() = tonode and
        tonode.getAnArg() = fromnode and
        func.getName() = name |
        name = "encode" or name = "decode" or
        name = "decodestring"
    )
}

/* tonode = str(fromnode)*/
private predicate to_str(ControlFlowNode fromnode, CallNode tonode) {
    tonode.getAnArg() = fromnode and
    exists(ClassObject str |
        tonode.getFunction().refersTo(str) |
        str = ClassObject::unicode() or str = ClassObject::bytes()
    )
}

/* tonode = fromnode[:] */
private predicate slice(ControlFlowNode fromnode, SubscriptNode tonode) {
    exists(Slice all |
        all = tonode.getIndex().getNode() and
        not exists(all.getStart()) and not exists(all.getStop()) and
        tonode.getValue() = fromnode
    )
}

/* tonode = os.path.join(..., fromnode, ...) */
private predicate os_path_join(ControlFlowNode fromnode, CallNode tonode) {
    exists(FunctionObject path_join |
        exists(ModuleObject os | os.getName() = "os" |
            os.getAttribute("path").(ModuleObject).getAttribute("join") = path_join
        ) |
        tonode = path_join.getACall() and tonode.getAnArg() = fromnode 
    )
}
