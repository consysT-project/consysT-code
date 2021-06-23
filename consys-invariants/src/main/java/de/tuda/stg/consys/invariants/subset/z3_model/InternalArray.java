package de.tuda.stg.consys.invariants.subset.z3_model;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_sort_kind;
import de.tuda.stg.consys.invariants.subset.Z3Checker;
import de.tuda.stg.consys.invariants.subset.visitors.IntegerValueVisitor;

/**
 * This class provides an intermediate representation of arrays.
 */
public class InternalArray extends InternalVar {

  /**
   * Enumerates possible operations that can be performed over the whole array, see {@link #combineValues(Combiner, ArrayExpr, Z3_sort_kind)}.
   */
  public enum Combiner {
    ADDITION,
    MULTIPLICATION,
    AND,
    OR
  }

  private int size;

  /**
   * Constructs an intermediate representation of an array.
   * @param name name of the array
   * @param arraySort Z3 sort of the array
   * @param size array size
   */
  public InternalArray(String name, ArraySort arraySort, int size) {
    super(name, arraySort);
    this.size = size;
  }

  /**
   * Constructs an intermediate representation of an array and uses a default size.
   * @param name name of the array
   * @param arraySort Z3 sort of the array
   */
  public InternalArray(String name, ArraySort arraySort) {
    super(name, arraySort);
    size = IntegerValueVisitor.ARRAY_DEFAULT_SIZE;
  }

  /**
   * This method takes two Z3 array constants and their size and returns a formula
   * that compares both arrays element wise from index 0 to size-1.
   * @param one the one array to compare
   * @param other the other array to compare
   * @param size the size of both arrays
   * @return A Z3 expression containing the element wise equality check of both arrays
   */
  public static BoolExpr sameFields(ArrayExpr one, ArrayExpr other, int size) {
    BoolExpr same = Z3Checker.context.mkTrue();
    for (int i = 0; i < size; i++) {
      same =
          Z3Checker.context.mkAnd(
              same,
              Z3Checker.context.mkEq(
                  Z3Checker.context.mkSelect(one, Z3Checker.context.mkInt(i)),
                  Z3Checker.context.mkSelect(other, Z3Checker.context.mkInt(i))));
    }
    return same;
  }

  /**
   * This method builds up a formula where one array and another are element wise equal up to index size-1 but may differ
   * at index changedIndex.
   * @param old the array to compare
   * @param neww the other array where one field has changed
   * @param changedIndex the index of the field that might have changed
   * @param size the size of both arrays
   * @return A Z3 expression that describes both arrays being equal at every index, except for changedIndex
   */
  public static BoolExpr oneFieldChanged(ArrayExpr old, ArrayExpr neww, int changedIndex, int size) {
    BoolExpr changed = Z3Checker.context.mkTrue();
    for (int i = 0; i < size && i != changedIndex; i++) {
      changed =
          Z3Checker.context.mkAnd(
              changed,
              Z3Checker.context.mkEq(
                  Z3Checker.context.mkSelect(old, Z3Checker.context.mkInt(i)),
                  Z3Checker.context.mkSelect(neww, Z3Checker.context.mkInt(i))));
    }
    return changed;
  }

  /**
   * Combines all values in the array using a {@link Combiner}. This can be used to sum up every value in the array for example.
   * Note that all values from index 0 to {@link #size} - 1 are used to build up the expression.
   * @param comb combiner to apply to all values
   * @param array the array on which the combiner is applied
   * @param rangeSort the Z3 sort of the elements of the array
   * @return A Z3 expression that contains the combination of all array values.
   */
  public Expr combineValues(Combiner comb, ArrayExpr array, Z3_sort_kind rangeSort) {
    switch (rangeSort) {
      case Z3_BOOL_SORT:
        BoolExpr retVal;
        switch (comb) {
          case AND:
            retVal = ctx.mkTrue();
            for (int i = 0; i < size; i++) {
              retVal = ctx.mkAnd(retVal, (BoolExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return retVal;
          case OR:
            retVal = ctx.mkFalse();
            for (int i = 0; i < size; i++) {
              retVal = ctx.mkOr(retVal, (BoolExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return retVal;
          default:
            return ctx.mkFalse();
        }

      case Z3_INT_SORT:
        IntExpr ret;
        switch (comb) {
          case ADDITION:
            ret = ctx.mkInt(0);
            for (int i = 0; i < size; i++) {
              ret = (IntExpr) ctx.mkAdd(ret, (IntExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return ret;
          case MULTIPLICATION:
            ret = ctx.mkInt(1);
            for (int i = 0; i < size; i++) {
              ret = (IntExpr) ctx.mkMul(ret, (IntExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return ret;
          default:
            return ctx.mkInt(-1);
        }

      case Z3_REAL_SORT:
        RealExpr real;
        switch (comb) {
          case ADDITION:
            real = ctx.mkReal(0);
            for (int i = 0; i < size; i++) {
              real = (RealExpr) ctx.mkAdd(real, (RealExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return real;
          case MULTIPLICATION:
            real = ctx.mkReal(1);
            for (int i = 0; i < size; i++) {
              real = (RealExpr) ctx.mkMul(real, (RealExpr) ctx.mkSelect(array, ctx.mkInt(i)));
            }
            return real;
          default:
            return ctx.mkReal(-1);
        }

      default:
        return ctx.mkInt(-1);
    }
  }

  @Override
  public ArrayExpr getOldValue() {
    return (ArrayExpr) oldValue;
  }

  @Override
  public ArrayExpr getOtherValue() {
    return (ArrayExpr) otherValue;
  }

  @Override
  public ArrayExpr getNewValue() {
    return (ArrayExpr) newValue;
  }

  @Override
  public ArrayExpr createCopy(String appendix) {
    return (ArrayExpr) super.createCopy(appendix);
  }

  public int getSize() {
    return size;
  }

  /**
   * Sets the size of the array object if it is greater than or equal to zero. If the value is negative, nothing changes.
   * @param size the new size of the array
   */
  public void setSize(int size) {
    if (size >= 0) {
      this.size = size;
    }
  }
}
