package de.tuda.stg.consys.invariants.subset;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.subset.model.ConstraintModel;
import de.tuda.stg.consys.invariants.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalClass;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalMethod;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;

public class PropertyModel {

	private final Context ctx;
	private final ConstraintModel model;

	public static boolean modelPrint = true;

	public PropertyModel(Context ctx, ConstraintModel model) {
		this.ctx = ctx;
		this.model = model;
	}

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


	/**
	 * Check that the initial state satisfies the class invariant
	 *
	 * <p>Initial(old) ==> I(old)
	 */
//	public static boolean checkInitialState() {
//		BoolExpr initialStatePreservesInvariant =
//				context.mkImplies(
//            /*
//            here, we want to make statements about the old state, that's why if the initial value constraints
//            and the invariant have been described in terms of the new state, we have to substitute them
//             */
//						(BoolExpr) clazz.getInitialValue().substitute(clazz.getNewState(), clazz.getOldState()),
//						(BoolExpr) clazz.getInvariant().substitute(clazz.getNewState(), clazz.getOldState()));
//
//		solver.reset();
//
//
//		private static Solver solver = context.mkSolver();
//
//		Status status = solver.check(context.mkNot(initialStatePreservesInvariant));
//
//
//
//		switch (status) {
//			case UNSATISFIABLE:
//				return true;
//			case SATISFIABLE:
//			{
//				if (modelPrint)
//					System.out.println("Initial state breaks invariant: " + solver.getModel());
//				return false;
//			}
//			case UNKNOWN:
//			{
//				if (modelPrint)
//					System.out.println(
//							"Something went wrong trying to prove that the initial state is invariant preserving: "
//									+ solver.getReasonUnknown());
//				return false;
//			}
//			default:
//				return false;
//		}
//	}

	/**
	 * Check that every method preserves the invariant in sequential execution
	 *
	 * <p>I(s0) && pre_m(s0) && post_m(s0, s1, res) => I(s1)
	 */
	public boolean checkInvariantSufficiency(MethodBinding binding) {
		MethodModel method = model.getClassModel().getMethod(binding)
				.orElseThrow(() -> new IllegalArgumentException("method not in class: "+ binding));

		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr res = method.getFreshResultConst().orElse(null);

		Expr[] quantified = res == null ? new Expr[] { s0, s1 } : new Expr[] { s0, s1, res };

		BoolExpr inner =
				ctx.mkImplies(
						ctx.mkAnd(
								model.getInvariant().apply(s0),
								model.getPrecondition(binding).apply(s0),
								model.getPostcondition(binding).apply(s0, s1, res)
						),
						model.getInvariant().apply(s1)
				);

		Expr formula = ctx.mkForall(quantified, inner, 1, null, null, null, null);

		boolean result = checkValidity(formula);
		return result;
	}


	/**
	 * Check that the initial state is mergeable with itself
	 *
	 * <p>initial(old) => pre_merge(old, old)
	 */
//	public static boolean checkSelfMergeable(InternalClass clazz) {
//		BoolExpr selfMergeable =
//				context.mkImplies(
//						(BoolExpr) clazz.getInitialValue().substitute(clazz.getNewState(), clazz.getOldState()),
//						(BoolExpr)
//								clazz
//										.getMergeFunction()
//										.getPreCondition()
//										// pre_merge(old, other) --> pre_merge(old, old)
//										.substitute(clazz.getOtherState(), clazz.getOldState()));
//
//		solver.reset();
//		Status status = solver.check(context.mkNot(selfMergeable));
//
//		switch (status) {
//			case UNSATISFIABLE:
//				return true;
//			case SATISFIABLE:
//				if (modelPrint)
//					System.out.println(
//							"The initial state cannot be merged with itself!: " + solver.getModel());
//				return false;
//			case UNKNOWN:
//				if (modelPrint)
//					System.out.println(
//							"Something went wrong trying to prove that the initial state can be merged with itself: "
//									+ solver.getReasonUnknown());
//			default:
//				return false;
//		}
//	}


	/**
	 * Check that the state resulting from a merge satisfies the invariant
	 *
	 * <p>I(s0) && I(s1) && pre_merge(s0, s1) && post_merge(s0, s1, s2) => I(s2)
	 */
	public boolean checkInvariantSufficientMerge() {
		MergeMethodModel method = model.getClassModel().getMergeMethod();

		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr s2 = model.getClassModel().getFreshConst("s2");

		Expr[] quantified = new Expr[] { s0, s1, s2 };

		BoolExpr inner =
				ctx.mkImplies(
						ctx.mkAnd(
								model.getInvariant().apply(s0),
								model.getInvariant().apply(s1),
								model.getMergePrecondition().apply(s0, s1),
								model.getMergePostcondition().apply(s0, s1, s2)
						),
						model.getInvariant().apply(s2)
				);

		Expr formula = ctx.mkForall(quantified, inner, 1, null, null, null, null);

		boolean result = checkValidity(formula);
		return result;
	}


	/**
	 *
	 * I(s0) & pre_m(s0) & post_m(s0, s1, res) => pre_merge(s0, s1)
	 */
	public boolean checkConcurrentStateMerge(MethodBinding binding) {
		MethodModel method = model.getClassModel().getMethod(binding)
				.orElseThrow(() -> new IllegalArgumentException("method not in class: "+ binding));

		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr res = method.getFreshResultConst().orElse(null);

		Expr[] quantified = res == null ? new Expr[] { s0, s1 } : new Expr[] { s0, s1, res };

		BoolExpr inner =
				ctx.mkImplies(
						ctx.mkAnd(
								model.getInvariant().apply(s0),
								model.getPrecondition(binding).apply(s0),
								model.getPostcondition(binding).apply(s0, s1, res)
						),
						model.getMergePrecondition().apply(s0, s1)
				);

		Expr formula = ctx.mkForall(quantified, inner, 1, null, null, null, null);

		boolean result = checkValidity(formula);
		return result;
	}



	/* Merge properties */

	/**
	 * Check that merging a state with itself results in the same state
	 *
	 * <p>I(s0) & post_merge(s0, s0, s1) ==> s0 == s1
	 */
//	public boolean checkMergeIdempotency() {
//		//TODO: Recheck this. This formula does not look right.
//		MergeMethodModel method = model.getClassModel().getMergeMethod();
//
//		Expr s0 = model.getClassModel().getFreshConst("s0");
//		Expr s1 = model.getClassModel().getFreshConst("s1");
//
//		Expr[] quantified = new Expr[] { s0, s1 };
//
//		BoolExpr inner =
//				ctx.mkImplies(
//						ctx.mkAnd(
//								model.getInvariant().apply(s0),
//								model.getMergePostcondition().apply(s0, s0, s1)
//						),
//						ctx.mkEq(s0, s1)
//				);
//
//		Expr formula = ctx.mkForall(quantified, inner, 1, null, null, null, null);
//
//		boolean result = checkValidity(formula);
//		return result;
//	}


	/**
	 * Check that the merge function is commutative.
	 *
	 * <p>post_merge(s0, s1, s2) && post_merge(s0, old2, new2) && old == old2 <br>
	 * ==> new == new2
	 */
//	public boolean checkMergeCommutativity() {
//		//TODO: Recheck this. This formula does not look right.
//		MergeMethodModel method = model.getClassModel().getMergeMethod();
//
//		Expr s0 = model.getClassModel().getFreshConst("s0");
//		Expr s1 = model.getClassModel().getFreshConst("s1");
//		Expr s2 = model.getClassModel().getFreshConst("s2");
//
//		Expr[] quantified = new Expr[] { s0, s1 };
//
//		BoolExpr inner =
//				ctx.mkImplies(
//						ctx.mkAnd(
//								model.getInvariant().apply(s0),
//								model.getMergePostcondition().apply(s0, s1, s0)
//						),
//						ctx.mkEq(s0, s1)
//				);
//
//		Expr formula = ctx.mkForall(quantified, inner, 1, null, null, null, null);
//
//		boolean result = checkValidity(formula);
//		return result;
//	}


	/**
	 * Check that the merge function is associative
	 *
	 * <p>post_merge(left1, left2, leftInner) && post_merge(leftInner, left3, leftOuter) &&
	 * post_merge(right1, rightInner, rightOuter) && post_merge(right2, right3, rightInner) && <br>
	 * left1 == right1 && left2 == right2 && left3 == right3 ==> leftOuter == rightOuter
	 */
//	public static boolean checkMergeAssociativity(InternalClass clazz) {
//		Expr[] left1 = new Expr[clazz.getVariables().size()];
//		Expr[] left2 = new Expr[clazz.getVariables().size()];
//		Expr[] left3 = new Expr[clazz.getVariables().size()];
//		Expr[] leftInner = new Expr[clazz.getVariables().size()];
//		Expr[] leftOuter = new Expr[clazz.getVariables().size()];
//
//		Expr[] right1 = new Expr[clazz.getVariables().size()];
//		Expr[] right2 = new Expr[clazz.getVariables().size()];
//		Expr[] right3 = new Expr[clazz.getVariables().size()];
//		Expr[] rightInner = new Expr[clazz.getVariables().size()];
//		Expr[] rightOuter = new Expr[clazz.getVariables().size()];
//
//		BoolExpr leftOneEqRightOne = context.mkTrue();
//		BoolExpr leftTwoEqRightTwo = context.mkTrue();
//		BoolExpr leftThreeEqRightThree = context.mkTrue();
//		BoolExpr leftOuterEqRightOuter = context.mkTrue();
//
//		int i = 0;
//		for (InternalVar var : clazz.getVariables()) {
//			Expr currentLeft1 = var.createCopy("_left1");
//			Expr currentLeft2 = var.createCopy("_left2");
//			Expr currentLeft3 = var.createCopy("_left3");
//			Expr currentLeftInner = var.createCopy("_leftInner");
//			Expr currentLeftOuter = var.createCopy("_leftOuter");
//			Expr currentRight1 = var.createCopy("_right1");
//			Expr currentRight2 = var.createCopy("_right2");
//			Expr currentRight3 = var.createCopy("_right3");
//			Expr currentRightInner = var.createCopy("_rightInner");
//			Expr currentRightOuter = var.createCopy("_rightOuter");
//
//			left1[i] = currentLeft1;
//			left2[i] = currentLeft2;
//			left3[i] = currentLeft3;
//			leftInner[i] = currentLeftInner;
//			leftOuter[i] = currentLeftOuter;
//			right1[i] = currentRight1;
//			right2[i] = currentRight2;
//			right3[i] = currentRight3;
//			rightInner[i] = currentRightInner;
//			rightOuter[i] = currentRightOuter;
//			i++;
//
//			if (var instanceof InternalArray) {
//				// left1 == right1
//				leftOneEqRightOne =
//						context.mkAnd(
//								leftOneEqRightOne,
//								InternalArray.sameFields(
//										(ArrayExpr) currentLeft1,
//										(ArrayExpr) currentRight1,
//										((InternalArray) var).getSize()));
//
//				// left2 == right2
//				leftTwoEqRightTwo =
//						context.mkAnd(
//								leftTwoEqRightTwo,
//								InternalArray.sameFields(
//										(ArrayExpr) currentLeft2,
//										(ArrayExpr) currentRight2,
//										((InternalArray) var).getSize()));
//
//				// left3 == right3
//				leftThreeEqRightThree =
//						context.mkAnd(
//								leftThreeEqRightThree,
//								InternalArray.sameFields(
//										(ArrayExpr) currentLeft3,
//										(ArrayExpr) currentRight3,
//										((InternalArray) var).getSize()));
//
//				// leftOuter == rightOuter
//				leftOuterEqRightOuter =
//						context.mkAnd(
//								leftOuterEqRightOuter,
//								InternalArray.sameFields(
//										(ArrayExpr) currentLeftOuter,
//										(ArrayExpr) currentRightOuter,
//										((InternalArray) var).getSize()));
//			} else {
//				leftOneEqRightOne =
//						context.mkAnd(leftOneEqRightOne, context.mkEq(currentLeft1, currentRight1));
//				leftTwoEqRightTwo =
//						context.mkAnd(leftTwoEqRightTwo, context.mkEq(currentLeft2, currentRight2));
//				leftThreeEqRightThree =
//						context.mkAnd(leftThreeEqRightThree, context.mkEq(currentLeft3, currentRight3));
//				leftOuterEqRightOuter =
//						context.mkAnd(leftOuterEqRightOuter, context.mkEq(currentLeftOuter, currentRightOuter));
//			}
//		}
//
//		BoolExpr subPostMergeLeftInner =
//				(BoolExpr)
//						clazz
//								.getMergeFunction()
//								.getPostCondition()
//								.substitute(clazz.getOldState(), left1)
//								.substitute(clazz.getOtherState(), left2)
//								.substitute(clazz.getNewState(), leftInner);
//		BoolExpr subPostMergeLeftOuter =
//				(BoolExpr)
//						clazz
//								.getMergeFunction()
//								.getPostCondition()
//								.substitute(clazz.getOldState(), leftInner)
//								.substitute(clazz.getOtherState(), left3)
//								.substitute(clazz.getNewState(), leftOuter);
//		BoolExpr subPostMergeRightOuter =
//				(BoolExpr)
//						clazz
//								.getMergeFunction()
//								.getPostCondition()
//								.substitute(clazz.getOldState(), right1)
//								.substitute(clazz.getOtherState(), rightInner)
//								.substitute(clazz.getNewState(), rightOuter);
//		BoolExpr subPostMergeRightInner =
//				(BoolExpr)
//						clazz
//								.getMergeFunction()
//								.getPostCondition()
//								.substitute(clazz.getOldState(), right2)
//								.substitute(clazz.getOtherState(), right3)
//								.substitute(clazz.getNewState(), rightInner);
//		BoolExpr mergeAssociativity =
//				context.mkImplies(
//						context.mkAnd(
//								subPostMergeLeftInner,
//								subPostMergeLeftOuter,
//								subPostMergeRightOuter,
//								subPostMergeRightInner,
//								leftOneEqRightOne,
//								leftTwoEqRightTwo,
//								leftThreeEqRightThree),
//						leftOuterEqRightOuter);
//
//		solver.reset();
//		Status status = solver.check(context.mkNot(mergeAssociativity));
//
//		switch (status) {
//			case UNSATISFIABLE:
//				return true;
//			case SATISFIABLE:
//				if (modelPrint)
//					System.out.println("The merge function is NOT associative: " + solver.getModel());
//				return false;
//			case UNKNOWN:
//				if (modelPrint)
//					System.out.println(
//							"Something went wrong trying to prove that the merge function is associative: "
//									+ solver.getReasonUnknown());
//			default:
//				return false;
//		}
//	}




	private boolean checkValidity(Expr<BoolSort> expr) {

		Solver solver = ctx.mkSolver();
		Status status = solver.check(ctx.mkNot(expr));

		switch (status) {
			case UNSATISFIABLE:
				return true;
			case SATISFIABLE:
				return false;
			case UNKNOWN:
				//throw new IllegalStateException("solving expression lead to an error: " + expr);
				System.err.println("Error solving " + expr);
				return false;
			default:
				//Does not exist
				throw new RuntimeException();
		}
	}


}
