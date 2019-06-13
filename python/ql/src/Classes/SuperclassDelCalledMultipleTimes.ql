/**
 * @name Multiple calls to __del__ during object destruction
 * @description A duplicated call to a super-class __del__ method may lead to class instances not be cleaned up properly.
 * @kind problem
 * @tags efficiency
 *       correctness
 * @problem.severity warning
 * @sub-severity high
 * @precision very-high
 * @id py/multiple-calls-to-delete
 */

import python
import MethodCallOrder


from ClassValue self, CallableValue multi
where 
multiple_calls_to_superclass_method(self, multi, "__del__") and
not multiple_calls_to_superclass_method(self.getBase(_), multi, "__del__") and
not exists(CallableValue better |
    multiple_calls_to_superclass_method(self, better, "__del__") and
    better.overrides(multi)
) and
not self.failedInference(_)
select self, "Class " + self.getName() + " may not be cleaned up properly as $@ may be called multiple times during destruction.",
multi, multi.toString()
