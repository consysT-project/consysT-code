package de.tuda.stg.consys.invariants.subset;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;

public class ClassProperties {

	private final Z3Binding smt;
	private final ClassConstraints model;


	public ClassProperties(Z3Binding smt, ClassConstraints model) {
		this.smt = smt;
		this.model = model;
	}



	/* Sequential properties */

	// The initial state has to satisfy the invariant.
	// init(s0) ==> I(s0)
	public boolean checkInitialSatisfiesInvariant() {
		Expr s0 = model.getClassModel().getFreshConst("s0");

		BoolExpr property =
				smt.ctx.mkImplies(
						model.getInitialCondition().apply(s0),
						model.getInvariant().apply(s0)
				);

		return smt.isValid(property);
	}

	// Applying a method sequentially cannot violate the invariant.
	// I(s0) && pre_m(s0) && post_m(s0, s0_new, _) => I(s0_new)
	public boolean checkMethodSatisfiesInvariant(MethodBinding binding) {
		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s0_new = model.getClassModel().getFreshConst("s0_new");

		BoolExpr property =
				smt.ctx.mkImplies(
						smt.ctx.mkAnd(
								model.getInvariant().apply(s0),
								model.getPrecondition(binding).apply(s0),
								model.getPostcondition(binding).apply(s0, s0_new, null)
						),
						model.getInvariant().apply(s0_new)
				);

		return smt.isValid(property);
	}

	// Applying merge sequentially cannot violate the invariant.
	// I(s0) && I(s1) && pre_merge(s0, s1) && post_merge(s0, s1, s0_new) => I(s0_new)
	public boolean checkMergeSatisfiesInvariant() {
		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr s0_new = model.getClassModel().getFreshConst("s0_new");

		BoolExpr property =
				smt.ctx.mkImplies(
						smt.ctx.mkAnd(
								model.getInvariant().apply(s0),
								model.getInvariant().apply(s1),
								model.getMergePrecondition().apply(s0, s1),
								model.getMergePostcondition().apply(s0, s1, s0_new)
						),
						model.getInvariant().apply(s0_new)
				);

		return smt.isValid(property);
	}

	/* Concurrent properties (i.e. predicates for mergability) */

	// The initial state has to be mergable.
	// init(s0) ==> pre_merge(s0, s0)
	public boolean checkInitialSatisfiesMergability() {
		Expr s0 = model.getClassModel().getFreshConst("s0");

		BoolExpr property =
				smt.ctx.mkImplies(
						model.getInitialCondition().apply(s0),
						model.getMergePrecondition().apply(s0 ,s0)
				);

		return smt.isValid(property);
	}



	// Applying a method does not violate the mergability.
	// If this property is violated then the method can not be executed concurrently.
	// pre_m(s0) & pre_merge(s0, s1) & post_m(s0, s0_new, res) => pre_merge(s0_new, s1)
	public boolean checkMethodSatisfiesMergability(MethodBinding binding) {
		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr s0_new = model.getClassModel().getFreshConst("s0_new");

		BoolExpr property =
				smt.ctx.mkImplies(
						smt.ctx.mkAnd(
								model.getPrecondition(binding).apply(s0),
								model.getMergePrecondition().apply(s0, s1),
								model.getPostcondition(binding).apply(s0, s0_new, null)
						),
						model.getMergePrecondition().apply(s0_new, s1)
				);

		return smt.isValid(property);
	}

	// Applying merge does not violate the mergability.
	// pre_merge(s0, s1) & post_merge(s0, s1, s0_new) => pre_merge(s0_new, s1)
	public boolean checkMergeSatisfiesMergability() {
		Expr s0 = model.getClassModel().getFreshConst("s0");
		Expr s1 = model.getClassModel().getFreshConst("s1");
		Expr s0_new = model.getClassModel().getFreshConst("s0_new");

		BoolExpr property =
				smt.ctx.mkImplies(
						smt.ctx.mkAnd(
								model.getMergePrecondition().apply(s0, s1),
								model.getMergePostcondition().apply(s0, s1, s0_new)
						),
						model.getMergePrecondition().apply(s0_new, s1)
				);

		return smt.isValid(property);
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
//				smt.ctx.mkImplies(
//						smt.ctx.mkAnd(
//								model.getInvariant().apply(s0),
//								model.getMergePostcondition().apply(s0, s0, s1)
//						),
//						smt.ctx.mkEq(s0, s1)
//				);
//
//		Expr formula = smt.ctx.mkForall(quantified, inner, 1, null, null, null, null);
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
//				smt.ctx.mkImplies(
//						smt.ctx.mkAnd(
//								model.getInvariant().apply(s0),
//								model.getMergePostcondition().apply(s0, s1, s0)
//						),
//						smt.ctx.mkEq(s0, s1)
//				);
//
//		Expr formula = smt.ctx.mkForall(quantified, inner, 1, null, null, null, null);
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







}
