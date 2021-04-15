package subset.z3_model;

import com.microsoft.z3.Expr;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

import java.util.HashMap;
import java.util.Map;

/**
 * This class is used to represent a scope in which already visited variables, return values and the
 * information whether or not the analysis is currently visiting a merge function are captured.
 */
public class InternalScope {

  /** contains currently visited class variables */
  private Map<String, InternalVar> classVariables;

  /** contains variables of local scope such as method arguments */
  private Map<String, Expr> localVariables;

  /** contains the return expressions of already visited methods */
  private Map<String, Expr> returnValues;

  /**
   * used to support return values of currently visited methods and use them in the specification.
   * See {@link subset.visitors.ModelGenerator#visit(JmlMethodDeclaration, ClassScope)}.
   */
  private Expr currentReturnVariable;

  /**
   * used to build up a return expression for a currently visited method in order to use them in
   * other parts of the specification See {@link
   * subset.visitors.FormulaGenerator#visitBinaryExpression(BinaryExpression, InternalScope)}.
   */
  private Expr currentReturnExpression;

  /**
   * flag that indicates if the analysis is visiting a merge function or not. This is used to enable
   * the use of the state depicting the other state incoming to merge.
   */
  public boolean insideMergeFunction = false;

  /** Constructs a fresh scope containing nothing. */
  public InternalScope() {
    classVariables = new HashMap<>();
    localVariables = new HashMap<>();
    returnValues = new HashMap<>();
  }

  /** Constructs a scope object with the given parameters. */
  public InternalScope(
      Map<String, InternalVar> classVariables,
      Map<String, Expr> localVariables,
      Map<String, Expr> returnValues,
      Expr currentReturnVariable,
      boolean insideMergeFunction) {
    this.classVariables = classVariables;
    this.localVariables = localVariables;
    this.returnValues = returnValues;
    this.currentReturnVariable = currentReturnVariable;
    this.insideMergeFunction = insideMergeFunction;
  }

  public void addClassVariable(String name, InternalVar variable) {
    classVariables.put(name, variable);
  }

  public void addLocalVariable(String name, Expr variable) {
    localVariables.put(name, variable);
  }

  public void addReturnValue(String name, Expr value) {
    returnValues.put(name, value);
  }

  public InternalVar getClassVariable(String name) {
    if (hasClassVariable(name)) return classVariables.get(name);
    return null;
  }

  public Expr getLocalVariable(String name) {
    if (hasLocalVariable(name)) return localVariables.get(name);
    return null;
  }

  public Expr getReturnValue(String name) {
    if (hasReturnValue(name)) return returnValues.get(name);
    return null;
  }

  public Expr getCurrentReturnVariable() {
    return currentReturnVariable;
  }

  public void setCurrentReturnVariable(Expr currentReturnVariable) {
    this.currentReturnVariable = currentReturnVariable;
  }

  public Expr getCurrentReturnExpression() {
    return currentReturnExpression;
  }

  public void setCurrentReturnExpression(Expr currentReturnExpression) {
    this.currentReturnExpression = currentReturnExpression;
  }

  public Map<String, InternalVar> getClassVariables() {
    return classVariables;
  }

  public Map<String, Expr> getLocalVariables() {
    return localVariables;
  }

  public Map<String, Expr> getReturnValues() {
    return returnValues;
  }

  /**
   * This method resets the local variables, return variable and return expression and is called
   * after a method visit has been finished.
   */
  public void clearLocalScope() {
    localVariables = new HashMap<>();
    currentReturnVariable = null;
    currentReturnExpression = null;
  }

  public boolean hasLocalVariable(String name) {
    return localVariables.containsKey(name);
  }

  public boolean hasClassVariable(String name) {
    return classVariables.containsKey(name);
  }

  public boolean hasReturnValue(String name) {
    return returnValues.containsKey(name);
  }

  public boolean hasVariable(String name) {
    return hasLocalVariable(name) || hasClassVariable(name);
  }
}
