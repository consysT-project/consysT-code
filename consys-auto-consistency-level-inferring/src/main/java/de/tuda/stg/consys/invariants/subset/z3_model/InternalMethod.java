package de.tuda.stg.consys.invariants.subset.z3_model;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.Z3Checker;

import java.util.HashMap;
import java.util.Map;

/**
 * Intermediate representation of a method that contains arguments, preconditions, postconditions
 * and potential return values.
 */
public class InternalMethod {
  private String name;
  private Context context = Z3Checker.context;

  private Map<String, Expr> arguments = new HashMap<String, Expr>();
  private Sort returnType;
  private Expr returnVariable;
  private Expr returnExpression;

  private BoolExpr preConditions = context.mkTrue();
  private BoolExpr postConditions = context.mkTrue();

  public InternalMethod(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public void setPreCondition(BoolExpr pre) {
    preConditions = pre;
  }

  public void setPostCondition(BoolExpr post) {
    postConditions = post;
  }

  public void addPostCondition(BoolExpr post) {
    postConditions = context.mkAnd(postConditions, post);
  }

  public BoolExpr getPreConditions() {
    return preConditions;
  }

  public BoolExpr getPostConditions() {
    return postConditions;
  }

  /**
   * Adds an argument to this method by creating a new Z3 constant that represents the argument.
   * @param name name of the argument
   * @param type type of the argument
   */
  public void addArgument(String name, Sort type) {
    if (type != null) arguments.put(name, context.mkConst(name, type));
  }

  /**
   * Sets the return type of the method if it is other than void. Afterwards, a Z3 constant representing the return
   * value is created.
   * @param sort the Z3 sort representing the method's return type
   */
  public void setReturnType(Sort sort) {
    if (sort != null) {
      returnType = sort;
      returnVariable = context.mkConst(name, sort);
    }
  }

  public Expr getReturnExpression() {
    return returnExpression;
  }

  public void setReturnExpression(Expr returnExpression) {
    this.returnExpression = returnExpression;
  }

  public Sort getReturnType() {
    return returnType;
  }

  public Expr getReturnVariable() {
    return returnVariable;
  }

  public Expr getArgument(String name) {
    return arguments.get(name);
  }
}
