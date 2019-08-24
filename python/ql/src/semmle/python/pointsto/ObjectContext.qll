import python
private import semmle.python.pointsto.PointsTo
private import semmle.python.objects.ObjectInternal


private cached newtype TPointsToContext =
    TMainContext()
    or
    TRuntimeContext()
    or
    TImportContext()
    or
    TObjectContext(ObjectInternal self, boolean runtime) {
        exists(CallNode call, AttrNode attr, PointsToContext caller |
            call.getFunction() = attr and 
            PointsToInternal::pointsTo(attr.getObject(), caller, self, _)
            |
            runtime = runtime(caller)
        )
    }
    or
    TTypeContext(ClassObjectInternal type) {
        exists(ObjectInternal obj, CallNode call |
            PointsToInternal::pointsTo(call.getArg(_), _, obj, _) and
            type = obj.getClass()
        )
    }

/** Points-to context. Context can be one of:
 *    * "main": Used for scripts.
 *    * "import": Use for non-script modules.
 *    * "default": Use for functions and methods without caller context.
 *    * object-sensitivity for methods
 *    * type-sensitivity for arguments of functions
 */
class PointsToContext extends TPointsToContext {

    cached string toString() {
        this = TMainContext() and result = "main"
        or
        this = TRuntimeContext() and result = "runtime"
        or
        this = TImportContext() and result = "import"
        or
        exists(ObjectInternal self, boolean runtime |
            this = TObjectContext(self, runtime)
            |
            result = self.toString() + "(runtime)" and runtime = true
            or
            result = self.toString() + "(import)" and runtime = false
        )
    }

    /** Holds if this is the "main" context. */
    predicate isMain() {
        this = TMainContext()
    }

    /** Holds if this is the "import" context. */
    predicate isImport() {
        this = TImportContext()
    }

    /** Holds if this is the "default" context. */
    predicate isRuntime() {
        this = TRuntimeContext()
    }

    predicate isCall() {
        this = TObjectContext(_, _)
        or
        this = TTypeContext(_)
    }

    predicate appliesToScope(Scope s) {
        /* Scripts */
        this = TMainContext() and maybe_main(s)
        or
        /* Modules and classes evaluated at import */
        s instanceof ImportTimeScope and this = TImportContext()
        or
        this = TRuntimeContext() and executes_in_runtime_context(s)
        or
        /* Called functions, regardless of their name */
        exists(BoundMethodObjectInternal callable |
            this = TObjectContext(callable.getSelf(), _) and
            s = callable.getScope()
        )
        or
        InterProceduralPointsTo::callsite_calls_function(_, _, s, this, _)
    }

    /** Holds if this context can apply to the CFG node `n`. */
    pragma [inline] 
    predicate appliesTo(ControlFlowNode n) {
        this.appliesToScope(n.getScope())
    }

    /** Holds if `call` is the call-site from which this context was entered and `caller` is the caller's context. */
    predicate fromCall(CallNode call, PointsToContext caller) {
        this.fromCall(call, _, caller)
    }

    /** Holds if `call` is the call-site from which this context was entered and `caller` is the caller's context. */
    predicate fromCall(CallNode call, PythonFunctionObjectInternal callee, PointsToContext caller) {
        exists(BoundMethodObjectInternal bm |
            call = bm.getACall(caller) and
            bm.getFunction() = callee and
            this = TObjectContext(bm.getSelf(), runtime(caller))
        )
    }

    predicate fromRuntime() {
        runtime(this) = false
    }

    predicate untrackableCall(CallNode call) {
        // TO DO...
        none()
    }

    CallNode getRootCall() {
        // TO DO...
        none()
    }
}

private boolean runtime(PointsToContext context) {
    context = TImportContext() and result = false
    or
    context = TRuntimeContext() and result = true
    or
    context = TObjectContext(_, result)
}


private predicate in_source(Scope s) {
    exists(s.getEnclosingModule().getFile().getRelativePath())
}

/** Holds if this scope can be executed in the default context.
 * All modules and classes executed at import time and
 * all "public" functions and methods, including those invoked by the VM.
 */
predicate executes_in_runtime_context(Function f) {
    /* "Public" scope, i.e. functions whose name starts not with an underscore, or special methods */
    (f.getName().charAt(0) != "_" or f.isSpecialMethod() or f.isInitMethod()) 
    and 
    in_source(f)
}

private predicate maybe_main(Module m) {
    exists(If i, Compare cmp, Name name, StrConst main |
        m.getAStmt() = i and i.getTest() = cmp |
        cmp.compares(name, any(Eq eq), main) and
        name.getId() = "__name__" and
        main.getText() = "__main__"
    )
}






