package de.tuda.stg.consys.invariants.subset;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalArray;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalClass;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalMethod;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalVar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * This class is used to implement proofs of properties that are to be analysed. Each proof for a
 * property of a given {@link InternalClass} consists of:
 *
 * <p>1. building up the formula that describes the property for the given class 2. check the
 * negation of the formula using the Z3 SMT solver 3. if the status is UNSAT, the property has been
 * proven, if it is SAT, then violations were found and if it is UNKNOWN, some other error or
 * undecidable problem were encountered
 */
public class Z3Checker {

  public enum ConsistencyLevel {
    WEAK,
    STRONG
  }

  public enum Monotonicity {
    MONOTONE, NOT_MONOTONE
  }

  public enum InvariantSufficiency {
    INVARIANT_SUFFICIENT, NOT_INVARIANT_SUFFICIENT
  }

  public static Context context = new Context();
  private static Solver solver = context.mkSolver();
  public static boolean modelPrint = true;

  public static boolean checkPreRequisities(InternalClass clazz) {
    return checkInitialState(clazz)
        && checkInvariantSufficiency(clazz)
        && checkMergeIdempotency(clazz)
        && checkMergeCommutativity(clazz)
        && checkMergeAssociativity(clazz)
        && checkSelfMergeable(clazz)
        && checkInvariantSufficientMerge(clazz)
        && checkMergeableMergedState(clazz);
  }

  /**
   * @return a mapping from each method name to its consistency level according to the formula
   *     describing the condition for weak objects
   */
  public static Map<String, ConsistencyLevel> checkWeakConsistencyForMethods(InternalClass clazz) {
    Map<String, ConsistencyLevel> result = new HashMap<>();
    for (InternalMethod m : clazz.getMethods()) {
      result.put(
          m.getName(),
          checkMergeableOperationState(clazz, m) ? ConsistencyLevel.WEAK : ConsistencyLevel.STRONG);
    }
    return result;
  }

  /**
   * @return map that maps each method name to its consistency level according to the property
   *     whether the method is monotone or not
   */
  public static Map<String, Monotonicity> checkMonotonicityForMethods(InternalClass clazz) {
    Map<String, Monotonicity> result = new HashMap<>();
    for (InternalMethod m : clazz.getMethods()) {
      result.put(
          m.getName(),
          checkMethodMonotonicity(clazz, m) ? Monotonicity.MONOTONE : Monotonicity.NOT_MONOTONE);
    }
    return result;
  }

  /**
   * @return a map that maps each method name to method names which are NOT mergeable with the
   *     method, i.e. conflicting methods
   */
  public static Map<String, List<String>> checkMergeabilityForMethods(InternalClass clazz) {
    Map<String, List<String>> result = new HashMap<>();
    List<String> currentConflicts = new ArrayList<>();
    for (InternalMethod m1 : clazz.getMethods()) {
      result.put(m1.getName(), currentConflicts);

      for (InternalMethod m2 : clazz.getMethods()) {
        if (!checkInterMethodMergeability(clazz, m1, m2)) {
          currentConflicts.add(m2.getName());
        }
      }

      currentConflicts = new ArrayList<>();
    }

    return result;
  }

  public static Map<String, InvariantSufficiency> checkInvariantSufficiencyForMethods(InternalClass clazz) {
    Map<String, InvariantSufficiency> result = new HashMap<>();

    for (InternalMethod m : clazz.getMethods()) {
      BoolExpr methodIsInvariantSufficient =
              context.mkImplies(
                      context.mkAnd(
                              (BoolExpr)
                                      // substitute new to old for the I(old) part
                                      clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                              m.getPreConditions(),
                              m.getPostConditions()),
                      // substitute old to new for the I(new) part
                      (BoolExpr) clazz.getInvariant().substitute(clazz.getOldState(), clazz.getNewState()));

      solver.reset();
      Status status = solver.check(context.mkNot(methodIsInvariantSufficient));
      switch (status) {
        case UNSATISFIABLE:
        {
          result.put(m.getName(), InvariantSufficiency.INVARIANT_SUFFICIENT);
          break;
        }
        case SATISFIABLE:
        {
          if (modelPrint)
            System.out.println(
                    "Method "
                            + m.getName()
                            + " breaks the invariant during sequential execution: "
                            + solver.getModel());
          result.put(m.getName(), InvariantSufficiency.NOT_INVARIANT_SUFFICIENT);
          break;
        }
        case UNKNOWN:
        {
          if (modelPrint)
            System.out.println(
                    "Something went wrong trying to prove invariant sufficiency for method "
                            + m.getName()
                            + ": "
                            + solver.getReasonUnknown());
          result.put(m.getName(), InvariantSufficiency.NOT_INVARIANT_SUFFICIENT);
          break;
        }
      }
    }
    return result;
  }

  /**
   * Check that the initial state satisfies the class invariant
   *
   * <p>Initial(old) ==> I(old)
   */
  public static boolean checkInitialState(InternalClass clazz) {
    BoolExpr initialStatePreservesInvariant =
        context.mkImplies(
            /*
            here, we want to make statements about the old state, that's why if the initial value constraints
            and the invariant have been described in terms of the new state, we have to substitute them
             */
            (BoolExpr) clazz.getInitialValue().substitute(clazz.getNewState(), clazz.getOldState()),
            (BoolExpr) clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()));

    solver.reset();
    Status status = solver.check(context.mkNot(initialStatePreservesInvariant));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        {
          if (modelPrint)
            System.out.println("Initial state breaks invariant: " + solver.getModel());
          return false;
        }
      case UNKNOWN:
        {
          if (modelPrint)
            System.out.println(
                "Something went wrong trying to prove that the initial state is invariant preserving: "
                    + solver.getReasonUnknown());
          return false;
        }
      default:
        return false;
    }
  }

  /**
   * Check that every method preserves the invariant in sequential execution
   *
   * <p>I(old) && pre_m(old) && post_m(old, new) => I(new)
   */
  public static boolean checkInvariantSufficiency(InternalClass clazz) {
    boolean isEveryMethodInvariantSufficient = true;

    for (InternalMethod m : clazz.getMethods()) {
      BoolExpr methodIsInvariantSufficient =
          context.mkImplies(
              context.mkAnd(
                  (BoolExpr)
                      // substitute new to old for the I(old) part
                      clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                  m.getPreConditions(),
                  m.getPostConditions()),
              // substitute old to new for the I(new) part
              (BoolExpr) clazz.getInvariant().substitute(clazz.getOldState(), clazz.getNewState()));

      solver.reset();
      Status status = solver.check(context.mkNot(methodIsInvariantSufficient));
      switch (status) {
        case UNSATISFIABLE:
          {
            break;
          }
        case SATISFIABLE:
          {
            if (modelPrint)
              System.out.println(
                  "Method "
                      + m.getName()
                      + " breaks the invariant during sequential execution: "
                      + solver.getModel());
            isEveryMethodInvariantSufficient = false;
            break;
          }
        case UNKNOWN:
          {
            if (modelPrint)
              System.out.println(
                  "Something went wrong trying to prove invariant sufficiency for method "
                      + m.getName()
                      + ": "
                      + solver.getReasonUnknown());
            isEveryMethodInvariantSufficient = false;
            break;
          }
      }
    }
    return isEveryMethodInvariantSufficient;
  }

  /**
   * Check that merging a state with itself results in the same state
   *
   * <p>post_merge(old, old, new) ==> new == old
   */
  public static boolean checkMergeIdempotency(InternalClass clazz) {
    BoolExpr newEqualsOldState = context.mkTrue();
    for (InternalVar var : clazz.getVariables()) {
      // array equality has to be made elementwise
      if (var instanceof InternalArray) {
        newEqualsOldState =
            context.mkAnd(
                newEqualsOldState,
                InternalArray.sameFields(
                    ((InternalArray) var).getNewValue(),
                    ((InternalArray) var).getOldValue(),
                    ((InternalArray) var).getSize()));
      } else {
        newEqualsOldState =
            context.mkAnd(newEqualsOldState, context.mkEq(var.getNewValue(), var.getOldValue()));
      }
    }

    BoolExpr mergeIsIdempotent =
        context.mkImplies(
            (BoolExpr)
                clazz
                    .getMergeFunction()
                    .getPostConditions()
                    .substitute(clazz.getOtherState(), clazz.getOldState()),
            newEqualsOldState);

    solver.reset();
    Status status = solver.check(context.mkNot(mergeIsIdempotent));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println("The merge function is NOT idempotent!: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove idempotency of the merge function: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that the merge function is commutative.
   *
   * <p>post_merge(old, other, new) && post_merge(other, old2, new2) && old == old2 <br>
   * ==> new == new2
   */
  public static boolean checkMergeCommutativity(InternalClass clazz) {
    Expr[] old2 = new Expr[clazz.getVariables().size()];
    Expr[] new2 = new Expr[clazz.getVariables().size()];
    BoolExpr oldEqOld2 = context.mkTrue();
    BoolExpr newEqNew2 = context.mkTrue();

    int i = 0;
    for (InternalVar var : clazz.getVariables()) {
      Expr currentOld2 = var.createCopy("_old2");
      Expr currentNew2 = var.createCopy("_new2");
      if (var instanceof InternalArray) {
        oldEqOld2 =
            context.mkAnd(
                oldEqOld2,
                InternalArray.sameFields(
                    ((InternalArray) var).getOldValue(),
                    (ArrayExpr) currentOld2,
                    ((InternalArray) var).getSize()));
        newEqNew2 =
            context.mkAnd(
                newEqNew2,
                InternalArray.sameFields(
                    ((InternalArray) var).getNewValue(),
                    (ArrayExpr) currentNew2,
                    ((InternalArray) var).getSize()));
      } else {
        oldEqOld2 = context.mkAnd(oldEqOld2, context.mkEq(var.getOldValue(), currentOld2));
        newEqNew2 = context.mkAnd(newEqNew2, context.mkEq(var.getNewValue(), currentNew2));
      }
      old2[i] = currentOld2;
      new2[i] = currentNew2;
      i++;
    }

    // post_merge(old, other, new) --> post_merge(other, old2, new2)
    BoolExpr substitutedPostMerge =
        (BoolExpr)
            clazz
                .getMergeFunction()
                .getPostConditions()
                .substitute(clazz.getOtherState(), old2) // other --> old2
                .substitute(clazz.getNewState(), new2) // new --> new2
                .substitute(clazz.getOldState(), clazz.getOtherState()); // old --> other

    BoolExpr mergeCommutativity =
        context.mkImplies(
            context.mkAnd(
                clazz.getMergeFunction().getPostConditions(), substitutedPostMerge, oldEqOld2),
            newEqNew2);

    solver.reset();
    Status status = solver.check(context.mkNot(mergeCommutativity));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println("The merge function is NOT commutative: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that the merge function is commutative: "
                  + solver.getReasonUnknown());
        return false;
      default:
        return false;
    }
  }

  /**
   * Check that the merge function is associative
   *
   * <p>post_merge(left1, left2, leftInner) && post_merge(leftInner, left3, leftOuter) &&
   * post_merge(right1, rightInner, rightOuter) && post_merge(right2, right3, rightInner) && <br>
   * left1 == right1 && left2 == right2 && left3 == right3 ==> leftOuter == rightOuter
   */
  public static boolean checkMergeAssociativity(InternalClass clazz) {
    Expr[] left1 = new Expr[clazz.getVariables().size()];
    Expr[] left2 = new Expr[clazz.getVariables().size()];
    Expr[] left3 = new Expr[clazz.getVariables().size()];
    Expr[] leftInner = new Expr[clazz.getVariables().size()];
    Expr[] leftOuter = new Expr[clazz.getVariables().size()];

    Expr[] right1 = new Expr[clazz.getVariables().size()];
    Expr[] right2 = new Expr[clazz.getVariables().size()];
    Expr[] right3 = new Expr[clazz.getVariables().size()];
    Expr[] rightInner = new Expr[clazz.getVariables().size()];
    Expr[] rightOuter = new Expr[clazz.getVariables().size()];

    BoolExpr leftOneEqRightOne = context.mkTrue();
    BoolExpr leftTwoEqRightTwo = context.mkTrue();
    BoolExpr leftThreeEqRightThree = context.mkTrue();
    BoolExpr leftOuterEqRightOuter = context.mkTrue();

    int i = 0;
    for (InternalVar var : clazz.getVariables()) {
      Expr currentLeft1 = var.createCopy("_left1");
      Expr currentLeft2 = var.createCopy("_left2");
      Expr currentLeft3 = var.createCopy("_left3");
      Expr currentLeftInner = var.createCopy("_leftInner");
      Expr currentLeftOuter = var.createCopy("_leftOuter");
      Expr currentRight1 = var.createCopy("_right1");
      Expr currentRight2 = var.createCopy("_right2");
      Expr currentRight3 = var.createCopy("_right3");
      Expr currentRightInner = var.createCopy("_rightInner");
      Expr currentRightOuter = var.createCopy("_rightOuter");

      left1[i] = currentLeft1;
      left2[i] = currentLeft2;
      left3[i] = currentLeft3;
      leftInner[i] = currentLeftInner;
      leftOuter[i] = currentLeftOuter;
      right1[i] = currentRight1;
      right2[i] = currentRight2;
      right3[i] = currentRight3;
      rightInner[i] = currentRightInner;
      rightOuter[i] = currentRightOuter;
      i++;

      if (var instanceof InternalArray) {
        // left1 == right1
        leftOneEqRightOne =
            context.mkAnd(
                leftOneEqRightOne,
                InternalArray.sameFields(
                    (ArrayExpr) currentLeft1,
                    (ArrayExpr) currentRight1,
                    ((InternalArray) var).getSize()));

        // left2 == right2
        leftTwoEqRightTwo =
            context.mkAnd(
                leftTwoEqRightTwo,
                InternalArray.sameFields(
                    (ArrayExpr) currentLeft2,
                    (ArrayExpr) currentRight2,
                    ((InternalArray) var).getSize()));

        // left3 == right3
        leftThreeEqRightThree =
            context.mkAnd(
                leftThreeEqRightThree,
                InternalArray.sameFields(
                    (ArrayExpr) currentLeft3,
                    (ArrayExpr) currentRight3,
                    ((InternalArray) var).getSize()));

        // leftOuter == rightOuter
        leftOuterEqRightOuter =
            context.mkAnd(
                leftOuterEqRightOuter,
                InternalArray.sameFields(
                    (ArrayExpr) currentLeftOuter,
                    (ArrayExpr) currentRightOuter,
                    ((InternalArray) var).getSize()));
      } else {
        leftOneEqRightOne =
            context.mkAnd(leftOneEqRightOne, context.mkEq(currentLeft1, currentRight1));
        leftTwoEqRightTwo =
            context.mkAnd(leftTwoEqRightTwo, context.mkEq(currentLeft2, currentRight2));
        leftThreeEqRightThree =
            context.mkAnd(leftThreeEqRightThree, context.mkEq(currentLeft3, currentRight3));
        leftOuterEqRightOuter =
            context.mkAnd(leftOuterEqRightOuter, context.mkEq(currentLeftOuter, currentRightOuter));
      }
    }

    BoolExpr subPostMergeLeftInner =
        (BoolExpr)
            clazz
                .getMergeFunction()
                .getPostConditions()
                .substitute(clazz.getOldState(), left1)
                .substitute(clazz.getOtherState(), left2)
                .substitute(clazz.getNewState(), leftInner);
    BoolExpr subPostMergeLeftOuter =
        (BoolExpr)
            clazz
                .getMergeFunction()
                .getPostConditions()
                .substitute(clazz.getOldState(), leftInner)
                .substitute(clazz.getOtherState(), left3)
                .substitute(clazz.getNewState(), leftOuter);
    BoolExpr subPostMergeRightOuter =
        (BoolExpr)
            clazz
                .getMergeFunction()
                .getPostConditions()
                .substitute(clazz.getOldState(), right1)
                .substitute(clazz.getOtherState(), rightInner)
                .substitute(clazz.getNewState(), rightOuter);
    BoolExpr subPostMergeRightInner =
        (BoolExpr)
            clazz
                .getMergeFunction()
                .getPostConditions()
                .substitute(clazz.getOldState(), right2)
                .substitute(clazz.getOtherState(), right3)
                .substitute(clazz.getNewState(), rightInner);
    BoolExpr mergeAssociativity =
        context.mkImplies(
            context.mkAnd(
                subPostMergeLeftInner,
                subPostMergeLeftOuter,
                subPostMergeRightOuter,
                subPostMergeRightInner,
                leftOneEqRightOne,
                leftTwoEqRightTwo,
                leftThreeEqRightThree),
            leftOuterEqRightOuter);

    solver.reset();
    Status status = solver.check(context.mkNot(mergeAssociativity));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println("The merge function is NOT associative: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that the merge function is associative: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that the initial state is mergeable with itself
   *
   * <p>initial(old) => pre_merge(old, old)
   */
  public static boolean checkSelfMergeable(InternalClass clazz) {
    BoolExpr selfMergeable =
        context.mkImplies(
            (BoolExpr) clazz.getInitialValue().substitute(clazz.getNewState(), clazz.getOldState()),
            (BoolExpr)
                clazz
                    .getMergeFunction()
                    .getPreConditions()
                    // pre_merge(old, other) --> pre_merge(old, old)
                    .substitute(clazz.getOtherState(), clazz.getOldState()));

    solver.reset();
    Status status = solver.check(context.mkNot(selfMergeable));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println(
              "The initial state cannot be merged with itself!: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that the initial state can be merged with itself: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that the state resulting from a merge satisfies the invariant
   *
   * <p>I(old) && I(other) && pre_merge(old, other) && post_merge(old, other, new) => I(new)
   */
  public static boolean checkInvariantSufficientMerge(InternalClass clazz) {
    BoolExpr invariantSufficientMerge =
        context.mkImplies(
            context.mkAnd(
                (BoolExpr)
                    // I(old)
                    clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                (BoolExpr)
                    // I(other)
                    clazz
                        .getInvariant()
                        .substitute(clazz.getOldState(), clazz.getOtherState())
                        .substitute(clazz.getNewState(), clazz.getOtherState()),
                clazz.getMergeFunction().getPreConditions(),
                clazz.getMergeFunction().getPostConditions()),
            // I(new)
            (BoolExpr) clazz.getInvariant().substitute(clazz.getOldState(), clazz.getNewState()));

    solver.reset();
    Status status = solver.check(context.mkNot(invariantSufficientMerge));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println(
              "There are state merges that break the invariant: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that state merging satisfies the invariant: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that the state resulting from a merge can be merged again
   *
   * <p>I(old) && I(other) && pre_merge(old, other) && post_merge(old, other, new) <br>
   * => I(new) && I(other) && (pre_merge(new, other) && pre_merge(new, old)) <br>
   * ==> new is LUB of both other and old
   */
  public static boolean checkMergeableMergedState(InternalClass clazz) {
    BoolExpr mergeableMergedState =
        context.mkImplies(
            context.mkAnd(
                (BoolExpr)
                    // I(old)
                    clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                (BoolExpr)
                    // I(other)
                    clazz
                        .getInvariant()
                        .substitute(clazz.getOldState(), clazz.getOtherState())
                        .substitute(clazz.getNewState(), clazz.getOtherState()),
                clazz.getMergeFunction().getPreConditions(),
                clazz.getMergeFunction().getPostConditions()),
            context.mkAnd(
                (BoolExpr)
                    // I(new)
                    clazz.getInvariant().substitute(clazz.getOldState(), clazz.getNewState()),
                (BoolExpr)
                    // I(other)
                    clazz
                        .getInvariant()
                        .substitute(clazz.getOldState(), clazz.getOtherState())
                        .substitute(clazz.getNewState(), clazz.getOtherState()),
                (BoolExpr)
                    // pre_merge(new, other)
                    clazz
                        .getMergeFunction()
                        .getPreConditions()
                        .substitute(clazz.getOldState(), clazz.getNewState()),
                (BoolExpr)
                    // pre_merge(new, old)
                    clazz
                        .getMergeFunction()
                        .getPreConditions()
                        .substitute(clazz.getOldState(), clazz.getNewState())
                        .substitute(clazz.getOtherState(), clazz.getNewState())));

    solver.reset();
    Status status = solver.check(context.mkNot(mergeableMergedState));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println("Merged state cannot be merged again: " + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that merged states can be merged again: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that the state resulting from a Method invocation can be merged. This constraint decides
   * whether or not a method can execute under weak consistency.
   *
   * <p>I(old) && I(other) && pre_m(old) && pre_merge(old, other) && post_m(old, new) <br>
   * => pre_merge(new, other)
   */
  public static boolean checkMergeableOperationState(InternalClass clazz, InternalMethod method) {
    BoolExpr mergeableOperationState =
        context.mkImplies(
            context.mkAnd(
                (BoolExpr)
                    // I(old)
                    clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                (BoolExpr)
                    // I(other)
                    clazz
                        .getInvariant()
                        .substitute(clazz.getOldState(), clazz.getOtherState())
                        .substitute(clazz.getNewState(), clazz.getOtherState()),
                // pre_m(old)
                method.getPreConditions(),
                // pre_merge(old, other)
                clazz.getMergeFunction().getPreConditions(),
                // post_m(old, new)
                method.getPostConditions()),

            // pre_merge(new, other)
            (BoolExpr)
                clazz
                    .getMergeFunction()
                    .getPreConditions()
                    .substitute(clazz.getOldState(), clazz.getNewState()));

    solver.reset();
    //if(method.getName().equals("withdraw"))
    //  System.out.println("The pre condition of the merge is: " + clazz.getMergeFunction().getPreConditions().toString());
    Status status = solver.check(context.mkNot(mergeableOperationState));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println(
              "Method "
                  + method.getName()
                  + " violates the invariant under weak consistency: "
                  + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that method "
                  + method.getName()
                  + " can be executed under weak consistency: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * Check that a method is monotone with respect to the lattice induced by merge
   *
   * <p>I(old) && pre_m(old) && post_m(old, new) && post_merge(old, new, postMerge) <br>
   * ==> new == postMerge
   */
  public static boolean checkMethodMonotonicity(InternalClass clazz, InternalMethod method) {
    Expr[] postMerge = clazz.getFreshState("_postMerge");
    BoolExpr newEqPostMerge = context.mkTrue();

    int i = 0;
    // for every variable, add equality constraint to build up the "new == postMerge" part
    for (InternalVar var : clazz.getVariables()) {
      if (var instanceof InternalArray && postMerge[i] instanceof ArrayExpr) {
        newEqPostMerge =
            context.mkAnd(
                newEqPostMerge,
                InternalArray.sameFields(
                    (ArrayExpr) postMerge[i],
                    ((InternalArray) var).getNewValue(),
                    ((InternalArray) var).getSize()));
      } else {
        newEqPostMerge =
            context.mkAnd(newEqPostMerge, context.mkEq(postMerge[i], var.getNewValue()));
      }

      i++;
    }

    BoolExpr methodMonotonicity =
        context.mkImplies(
            context.mkAnd(
                (BoolExpr)
                    // I(old)
                    clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                method.getPreConditions(),
                method.getPostConditions(),
                (BoolExpr)
                    // post_merge(old, other, new) --> post_merge(old, new, postMerge)
                    clazz
                        .getMergeFunction()
                        .getPostConditions()
                        .substitute(clazz.getNewState(), postMerge)
                        .substitute(clazz.getOtherState(), clazz.getNewState())),
            newEqPostMerge);

    solver.reset();
    Status status = solver.check(context.mkNot(methodMonotonicity));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println(
              "The method "
                  + method.getName()
                  + " is not monotone w.r.t to lattice induced by merge: "
                  + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that method is monotone: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }

  /**
   * I(old) && pre_m1(old) && post_m1(old, new) && <br>
   * I(old2) && pre_m2(old2) && post_m2(old2, new2) && post_merge(new, new2, afterMerge) <br>
   * ==> I(afterMerge)
   */
  public static boolean checkInterMethodMergeability(
      InternalClass clazz, InternalMethod m1, InternalMethod m2) {
    Expr[] oldM2 = clazz.getFreshState("oldM2");
    Expr[] newM2 = clazz.getFreshState("newM2");
    Expr[] afterMerge = clazz.getFreshState("afterMerge");

    BoolExpr interMethodMergeability =
        context.mkImplies(
            context.mkAnd(
                (BoolExpr)
                    clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()),
                m1.getPreConditions(),
                m1.getPostConditions(),
                (BoolExpr)
                    clazz
                        .getInvariant()
                        .substitute(clazz.getNewState(), clazz.getOldState())
                        .substitute(clazz.getOldState(), oldM2),
                (BoolExpr)
                    m2.getPreConditions()
                        .substitute(clazz.getOldState(), oldM2)
                        .substitute(clazz.getNewState(), newM2),
                (BoolExpr)
                    m2.getPostConditions()
                        .substitute(clazz.getOldState(), oldM2)
                        .substitute(clazz.getNewState(), newM2),
                (BoolExpr)
                    clazz
                        .getMergeFunction()
                        .getPostConditions()
                        .substitute(clazz.getNewState(), afterMerge)
                        .substitute(clazz.getOtherState(), newM2)
                        .substitute(clazz.getOldState(), clazz.getNewState())),
            (BoolExpr)
                clazz
                    .getInvariant()
                    .substitute(clazz.getNewState(), afterMerge)
                    .substitute(clazz.getOldState(), afterMerge));

    solver.reset();
    Status status = solver.check(context.mkNot(interMethodMergeability));

    switch (status) {
      case UNSATISFIABLE:
        return true;
      case SATISFIABLE:
        if (modelPrint)
          System.out.println(
              "The methods  "
                  + m1.getName()
                  + " and "
                  + m2.getName()
                  + " are not mergeable under concurrent execution "
                  + solver.getModel());
        return false;
      case UNKNOWN:
        if (modelPrint)
          System.out.println(
              "Something went wrong trying to prove that methods: "
                  + m1.getName()
                  + " and "
                  + m2.getName()
                  + " are mergeable under concurrent execution: "
                  + solver.getReasonUnknown());
      default:
        return false;
    }
  }
}
