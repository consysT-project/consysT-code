package de.tuda.stg.consys.invariants.subset.visitors;

import de.tuda.stg.consys.invariants.subset.z3_model.InternalScope;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.IntLiteral;

/**
 * This visitor is used to calculate integer values from the specification. This is for example used to determine
 * the array size or an index.
 */
public class IntegerValueVisitor {
  public static final int ARRAY_DEFAULT_SIZE = 10;
  public static final int UNKNOWN_SIZE = -1;

  /**
   * Overall visit expression that delegates the visit calls to the appropriate visitXYZ(...) method. If the
   * expression has no special visit method, {@link #UNKNOWN_SIZE} is returned.
   * @param expression the expression to translate to an integer
   * @param scope the scope of the intermediate representation
   * @return the result of the delegated visit call or {@link #UNKNOWN_SIZE}.
   */
  public int visitExpression(Expression expression, InternalScope scope) {
    if (expression instanceof IntLiteral) {
      return ((IntLiteral) expression).value;
    }
    if (expression instanceof BinaryExpression) {
      return visitBinaryExpression((BinaryExpression) expression, scope);
    }

    return UNKNOWN_SIZE;
  }

  /**
   * evaluates binary expressions to their integer result
   * @param binaryExpression the expression to evaluate
   * @param scope the scope of the intermediate representation
   * @return the result of the evaluation or {@link #UNKNOWN_SIZE} if something went wrong
   */
  public int visitBinaryExpression(BinaryExpression binaryExpression, InternalScope scope) {
    int left = visitExpression(binaryExpression.left, scope);
    int right = visitExpression(binaryExpression.right, scope);

    if (left == UNKNOWN_SIZE || right == UNKNOWN_SIZE) {
      return UNKNOWN_SIZE;
    }

    String operator = binaryExpression.operatorToString();
    switch (operator) {
      case "+" : return left + right;
      case "-" : return left - right;
      case "*": return left * right;
      case "/": return left / right;
      case "%": return left % right;
      default: return UNKNOWN_SIZE;
    }
  }
}
