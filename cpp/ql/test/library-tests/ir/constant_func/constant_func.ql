import default
import semmle.code.cpp.ir.IR
import semmle.code.cpp.ir.internal.IntegerConstant

language[monotonicAggregates]
IntValue getConstantValue(Instruction instr) {
  result = instr.(IntegerConstantInstruction).getValue().toInt() or
  exists(BinaryInstruction binInstr, IntValue left, IntValue right |
    binInstr = instr and
    left = getConstantValue(binInstr.getLeftOperand()) and
    right = getConstantValue(binInstr.getRightOperand()) and
    (
      binInstr instanceof AddInstruction and result = add(left, right) or
      binInstr instanceof SubInstruction and result = sub(left, right) or
      binInstr instanceof MulInstruction and result = mul(left, right) or
      binInstr instanceof DivInstruction and result = div(left, right)
    )
  ) or
  result = getConstantValue(instr.(CopyInstruction).getSourceValue()) or
  exists(PhiInstruction phi |
    phi = instr and
    result = max(PhiOperand operand | operand = phi.getAnOperand() | getConstantValue(operand.getDefinitionInstruction())) and
    result = min(PhiOperand operand | operand = phi.getAnOperand() | getConstantValue(operand.getDefinitionInstruction()))
  )
}

from FunctionIR funcIR, int value
where 
  value = getValue(getConstantValue(funcIR.getReturnInstruction().(ReturnValueInstruction).getReturnValue()))
select funcIR, value
