
import python

from Stmt s, Expr e
where e = s.getASubExpression()
select s.toString(), e.toString(), e.getASubExpression*().toString(), s.getLocation().getStartLine()