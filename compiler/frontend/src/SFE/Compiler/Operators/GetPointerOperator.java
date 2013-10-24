package SFE.Compiler.Operators;

import SFE.Compiler.AnyType;
import SFE.Compiler.CompileTimeOperator;
import SFE.Compiler.Expression;
import SFE.Compiler.LvalExpression;
import SFE.Compiler.Pointer;
import SFE.Compiler.StatementBuffer;
import SFE.Compiler.Type;

public class GetPointerOperator extends Operator implements CompileTimeOperator{
  public int arity() {
    return 1;
  }
  public int priority() {
    throw new RuntimeException("Not implemented");
  }
  public Type getType(Object obj) {
    //Not determinate type -> should return AnyType.
    return new AnyType();
  }
  public Expression fieldEltAt(Expression expression, int i) {
    throw new RuntimeException("Not yet implemented");
  }
  public Expression inlineOp(StatementBuffer assignments, Expression... args) {
    return resolve(args);
  }
  public Pointer resolve(Expression ... args) {
    LvalExpression a = LvalExpression.toLvalExpression(args[0]);
    int location = Pointer.getMemoryLocation(a);
    return new Pointer(a.getType(), new LvalExpression[]{a}, location, location);
  }
}
