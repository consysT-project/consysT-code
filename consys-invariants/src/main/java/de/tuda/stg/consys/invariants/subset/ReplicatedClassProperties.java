package de.tuda.stg.consys.invariants.subset;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.ReplicatedClassModel;
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
			properties.add(methodSatisfiesMergability(m.getBinding()));
		});
		properties.add(mergeSatisfiesMergability());
	}


	// Applying merge sequentially cannot violate the invariant.
	// I(s0) && I(s1) && pre_merge(s0, s1) && post_merge(s0, s1, s0_new) => I(s0_new)
	public Property mergeSatisfiesInvariant() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		return new ClassProperty("invariant/merge",
				model.ctx.mkForall(
						new Expr[] {s0, s1, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getInvariant().apply(s1),
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
	}

	/* Concurrent properties (i.e. predicates for mergability) */

	// The initial state has to be mergable.
	// init(s0) ==> pre_merge(s0, s0)
	public Property initialSatisfiesMergability() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");

		return new ClassProperty("mergability/initial",
				model.ctx.mkForall(
						new Expr[] {s0},
						model.ctx.mkImplies(
								constraints.getInitialCondition().apply(s0),
								constraints.getMergePrecondition().apply(s0 ,s0)
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
	// inv(s0) & inv(s1) & pre_m(s0) & pre_merge(s0, s1) & post_m(s0, s0_new, _) => pre_merge(s0_new, s1)
	public Property methodSatisfiesMergability(MethodBinding binding) {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s1 = constraints.getClassModel().toFreshConst("s1");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		return new MethodProperty("mergability/method",
				binding,
				model.ctx.mkForall(
						new Expr[] {s0, s1, s0_new},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInvariant().apply(s0),
										constraints.getInvariant().apply(s1),
										constraints.getPrecondition(binding).apply(s0),
										constraints.getMergePrecondition().apply(s0, s1),
										constraints.getPostcondition(binding).apply(s0, s0_new, null)
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
										constraints.getInvariant().apply(s1),
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



}
