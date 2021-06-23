package de.tuda.stg.consys.invariants.subset.z3_model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.Z3Checker;

/**
 * Class capturing relevant properties of class variables in {@link InternalClass}. The relevant
 * properties are name, type and Z3 constants that describe the prestate, poststate and another
 * state for merge.
 */
public class InternalVar {
  protected String name;
  protected Expr oldValue;
  protected Expr otherValue;
  protected Expr newValue;
  protected Sort sort;

  protected Context ctx = Z3Checker.context;

  /**
   * Empty constructor actually used to construct {@link InternalConstant}. For constructing objects
   * of this class, see {@link #InternalVar(String, Sort)}.
   */
  protected InternalVar() {
    // empty for constants
  }

  /**
   * Constructs a data representation of class variables.
   *
   * @param name name of the variable
   * @param sort Z3 type of the variable
   */
  public InternalVar(String name, Sort sort) {
    this.name = name;
    this.oldValue = ctx.mkConst("old_" + name, sort);
    this.otherValue = ctx.mkConst("other_" + name, sort);
    this.newValue = ctx.mkConst("new_" + name, sort);
    this.sort = sort;
  }

  public String getName() {
    return name;
  }

  public Expr getOldValue() {
    return oldValue;
  }

  public Expr getOtherValue() {
    return otherValue;
  }

  public Expr getNewValue() {
    return newValue;
  }

  /**
   * Creates a new Z3 constant that has the same type and beginning of the name as every other
   * constant for this variable.
   *
   * @param appendix String that is appended to the {@link #name}.
   * @return a new Z3 constant with the same type and similar name.
   */
  public Expr createCopy(String appendix) {
    return ctx.mkConst(name + appendix, oldValue.getSort());
  }

  public Sort getSort() {
    return sort;
  }
}
