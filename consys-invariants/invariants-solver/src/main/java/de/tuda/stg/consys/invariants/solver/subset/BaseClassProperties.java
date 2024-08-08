package de.tuda.stg.consys.invariants.solver.subset;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.constraints.BaseClassConstraints;
import de.tuda.stg.consys.invariants.solver.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.logging.Logger;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;

import java.util.List;

public class BaseClassProperties<CModel extends BaseClassModel, CConstraints extends BaseClassConstraints<CModel>> extends ClassProperties<CModel, CConstraints> {

	public BaseClassProperties(ProgramModel model, CConstraints constraints) {
		super(model, constraints);
	}

	@Override
	protected void addProperties(List<Property> properties) {
		properties.add(initialSatisfiesInvariant());
		getClassModel().getMethods().forEach(m -> {
			properties.add(methodSatisfiesInvariant(m.getBinding()));
		});
	}

	/* Sequential properties */

	// The initial state has to satisfy the invariant.
	// init(s0) ==> I(s0)
	private Property initialSatisfiesInvariant() {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		return new ClassProperty("(i0) invariant/initial",
				model.ctx.mkForall(
						new Expr[] {s0},
						model.ctx.mkImplies(
								model.ctx.mkAnd(
										constraints.getInitialCondition().apply(s0),
										constraints.getFieldInvariant().apply(s0)
								),
								constraints.getInvariant().apply(s0)
						),
						1,
						null,
						null,
						null,
						null
				)
		);
	}

	// Applying a method sequentially cannot violate the invariant.
	// I(s0) && pre_m(s0) && post_m(s0, s0_new, _) => I(s0_new)
	private Property methodSatisfiesInvariant(MethodBinding binding) {
		Expr s0 = constraints.getClassModel().toFreshConst("s0");
		Expr s0_new = constraints.getClassModel().toFreshConst("s0_new");

		var returnSort = constraints.getClassModel().getMethod(binding).get().getReturnType().toSort();
		Expr[] forallArgs;
		Expr ret = null;
		if (model.types.voidType().toSort().equals(returnSort)) {
			forallArgs = new Expr[] {s0, s0_new};
		} else {
			ret = model.ctx.mkFreshConst("ret", returnSort);
			forallArgs = new Expr[] {s0, s0_new, ret};
		}

		var expr = model.ctx.mkForall(
				forallArgs,
				model.ctx.mkImplies(
						model.ctx.mkAnd(
								constraints.getInvariant().apply(s0),
								constraints.getFieldInvariant().apply(s0),
								constraints.getPrecondition(binding).apply(s0),
								constraints.getPostcondition(binding).apply(s0, s0_new, ret)
						),
						constraints.getInvariant().apply(s0_new)
				),
				1,
				null,
				null,
				null,
				null
		);

		Logger.info("(i1) invariant/method <" + String.valueOf(binding.shortReadableName()) + "> expression is:\n" + expr);

		return new MethodProperty("(i1) invariant/method", binding, expr);
	}


}
