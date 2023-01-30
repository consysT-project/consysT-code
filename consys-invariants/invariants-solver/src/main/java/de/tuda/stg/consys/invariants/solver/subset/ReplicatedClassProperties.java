package de.tuda.stg.consys.invariants.solver.subset;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.constraints.ReplicatedClassConstraints;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ReplicatedClassModel;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;

import java.util.List;

public class ReplicatedClassProperties<CModel extends ReplicatedClassModel, CConstraints extends ReplicatedClassConstraints<CModel>> extends BaseClassProperties<CModel, CConstraints> {

	public ReplicatedClassProperties(ProgramModel model, CConstraints constraints) {
		super(model, constraints);
	}

	@Override
	protected void addProperties(List<Property> properties) {
		super.addProperties(properties);

		properties.add(mergeSatisfiesInvariant());

		properties.add(initialSatisfiesMergability());
		getClassModel().getMethods().forEach(m -> {
			properties.add(methodSatisfiesWeakMergability(m.getBinding()));
			properties.add(methodSatisfiesStrongMergability(m.getBinding()));
		});
		properties.add(mergeSatisfiesMergability());

		if (model.config.SOLVER__CHECK_MERGE_PROPERTIES) {
			properties.add(mergeAssociative());
			properties.add(mergeCommutative());
			properties.add(mergeIdempotent());
		}
	}


	// Applying merge sequentially cannot violate the invariant.
	// I(s0) && I(s1) && pre_merge(s0, s1) && post_merge(s0, s1, s0_new) => I(s0_new)
	public Property mergeSatisfiesInvariant() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		var result = new ClassProperty("invariant/merge",
				model.ctx.mkForall(
						new Expr[] {s0, s1, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getFieldInvariant().apply(s0),
										constraints.getInvariant().apply(s1),
										constraints.getFieldInvariant().apply(s1),
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getMergePostcondition().apply(s0, s1, s0_new)
								),
								constraints.getInvariant().apply(s0_new)
						),
						1,
						null,
						null,
						null,
						null
				)
		);

		return result;
	}

	/* Concurrent properties (i.e. predicates for mergability) */

	// The initial state has to be mergable.
	// init(s0) ==> pre_merge(s0, s0)
	public Property initialSatisfiesMergability() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");

		var result = new ClassProperty("mergability/initial",
				model.ctx.mkForall(
						new Expr[] {s0},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInitialCondition().apply(s0),
										constraints.getInvariant().apply(s0),
										constraints.getFieldInvariant().apply(s0)
								),
								constraints.getMergePrecondition().apply(s0 ,s0)
						),
						1,
						null,
						null,
						null,
						null
				)

		);

		return result;
	}



	// Applying a method does not violate the mergability.
	// If this property is violated then the method can not be executed concurrently.
	// inv(s0) & inv(s1) & pre_m(s0) & pre_merge(s0, s1) & post_m(s0, s0_new, _) => pre_merge(s0_new, s1)
	public Property methodSatisfiesWeakMergability(MethodBinding binding) {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");


		var returnSort = constraints.getClassModel().getMethod(binding).get().getReturnType().toSort();
		Expr[] forallArgs;
		Expr ret = null;
		if (model.types.voidType().toSort().equals(returnSort)) {
			forallArgs = new Expr[] {s0, s1, s0_new};
		} else {
			ret = model.ctx.mkFreshConst("ret", returnSort);
			forallArgs = new Expr[] {s0, s1, s0_new, ret};
		}

		return new MethodProperty("mergability/weak/method",
				binding,
				model.ctx.mkForall(
						forallArgs,
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getFieldInvariant().apply(s0),
										constraints.getInvariant().apply(s1),
										constraints.getFieldInvariant().apply(s1),
										constraints.getInvariant().apply(s0_new),
										constraints.getFieldInvariant().apply(s0_new),
										constraints.getPrecondition(binding).apply(s0),
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getPostcondition(binding).apply(s0, s0_new, ret)
								),
								constraints.getMergePrecondition().apply(s0_new, s1)
						),
						1,
						null,
						null,
						null,
						null
				)

		);
	}


	// Applying a method does not violate the mergability.
	// If this property is violated then the method can not be executed concurrently.
	// inv(s0) & inv(s1) & pre_merge(s0, s1) & post_merge(s0, s1, s2) & pre_m(s2) & post_m(s2, s2_new, _) => pre_merge(s2_new, s1)
	// inv(s) & pre_m(s) & post_m(s, s_new, _) => pre_merge(s_new, s1)
	public Property methodSatisfiesStrongMergability(MethodBinding binding) {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s2 = constraints.getClassModel().toFreshConst("s2");
		Expr s2_new = constraints.getClassModel().toFreshConst("s2_new");


		var returnSort = constraints.getClassModel().getMethod(binding).get().getReturnType().toSort();
		Expr[] forallArgs;
		Expr ret = null;
		if (model.types.voidType().toSort().equals(returnSort)) {
			forallArgs = new Expr[] {s0, s1, s2, s2_new};
		} else {
			ret = model.ctx.mkFreshConst("ret", returnSort);
			forallArgs = new Expr[] {s0, s1, s2, s2_new, ret};
		}

		return new MethodProperty("mergability/strong/method",
				binding,
				model.ctx.mkForall(
						forallArgs,
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getFieldInvariant().apply(s0),

										constraints.getInvariant().apply(s1),
										constraints.getFieldInvariant().apply(s1),

										constraints.getInvariant().apply(s2),
										constraints.getFieldInvariant().apply(s2),

										constraints.getInvariant().apply(s2_new),
										constraints.getFieldInvariant().apply(s2_new),

										constraints.getMergePrecondition().apply(s0, s1),

										constraints.getMergePostcondition().apply(s0, s1, s2),


										constraints.getPrecondition(binding).apply(s2),
										constraints.getPostcondition(binding).apply(s2, s2_new, ret)
								),
								constraints.getMergePrecondition().apply(s2_new, s1)
						),
						1,
						null,
						null,
						null,
						null
				)

		);
	}

	// Applying merge does not violate the mergability.
	// inv(s0) & inv(s1) & pre_merge(s0, s1) & post_merge(s0, s1, s0_new) => pre_merge(s0_new, s1)
	public Property mergeSatisfiesMergability() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		return new ClassProperty("mergability/merge",
				model.ctx.mkForall(
						new Expr[] {s0, s1, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getFieldInvariant().apply(s0),
										constraints.getInvariant().apply(s1),
										constraints.getFieldInvariant().apply(s1),
										constraints.getInvariant().apply(s0_new),
										constraints.getFieldInvariant().apply(s0_new),
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getMergePostcondition().apply(s0, s1, s0_new)
								),
								constraints.getMergePrecondition().apply(s0_new, s1)
						),
						1,
						null,
						null,
						null,
						null
				)
		);
	}


	public Property mergeAssociative() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s2 = constraints.getClassModel().toFreshConst("s2");
		Expr s0_a_new = constraints.getClassModel().toFreshConst("s0_a_new");
		Expr s0_b_new = constraints.getClassModel().toFreshConst("s0_b_new");
		Expr s1_a_new = constraints.getClassModel().toFreshConst("s1_a_new");
		Expr s1_b_new = constraints.getClassModel().toFreshConst("s1_b_new");

		return new ClassProperty("property/merge/associativity",
				model.ctx.mkForall(
						new Expr[] {s0, s1, s2, s0_a_new, s0_b_new, s1_a_new, s1_b_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getMergePostcondition().apply(s0, s1, s0_a_new),
										constraints.getMergePostcondition().apply(s0_a_new, s2, s0_b_new),
										constraints.getMergePostcondition().apply(s0, s1_a_new, s1_b_new),
										constraints.getMergePostcondition().apply(s1, s2, s1_a_new)
								),
								model.ctx.mkEq(s0_b_new, s1_b_new)
						),
						1,
						null,
						null,
						null,
						null
				)
		);
	}

	public Property mergeCommutative() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");
		Expr s1_new = constraints.getClassModel().toFreshConst("s1_new");

		return new ClassProperty("property/merge/commutativity",
				model.ctx.mkForall(
						new Expr[] {s0, s1, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getMergePostcondition().apply(s0, s1, s0_new),
										constraints.getMergePostcondition().apply(s1, s0, s1_new)
								),
								model.ctx.mkEq(s0_new, s1_new)
						),
						1,
						null,
						null,
						null,
						null
				)
		);
	}

	public Property mergeIdempotent() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		return new ClassProperty("property/merge/idempotence",
				model.ctx.mkForall(
						new Expr[] {s0, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getMergePrecondition().apply(s0, s0),
										constraints.getMergePostcondition().apply(s0, s0, s0_new)
								),
								model.ctx.mkEq(s0_new, s0)
						),
						1,
						null,
						null,
						null,
						null
				)
		);
	}



}
