package de.tuda.stg.consys.invariants.solver.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ReplicatedClassModel;
import de.tuda.stg.consys.invariants.solver.subset.parser.MergeMethodPostconditionExpressionParser;
import de.tuda.stg.consys.invariants.solver.subset.parser.MergeMethodPreconditionExpressionParser;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

public class ReplicatedClassConstraints<CModel extends ReplicatedClassModel> extends BaseClassConstraints<CModel> {

	/** Merge precondtion */
	private final MergePreconditionModel mergePrecondition;
	/** Merge postcondition */
	private final MergePostconditionModel mergePostcondition;


	public ReplicatedClassConstraints(ProgramModel model, CModel classModel) {
		super(model, classModel);

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the merge pre/postcondition.
		MergeMethodModel mergeModel = classModel.getMergeMethod();
		mergePrecondition = handleMergePrecondition(mergeModel);
		mergePostcondition = handleMergePostcondition(mergeModel);

		var sOld = classModel.toFreshConst("s_old");
		var sOther = classModel.toFreshConst("s_other");
		var sNew = classModel.toFreshConst("s_new");

		var appToState = mergeModel.makeApplyReturnState(sOld, new Expr[] {sOther}).orElseThrow();

		Expr[] forallArguments = new Expr[] {sOld, sOther};

		Expr expr = mergePostcondition.apply(sOld, sOther, appToState);


		var assertion =
				model.ctx.mkForall(
						forallArguments,
						expr,
						1,
						null,
						null,
						null,
						null
				);

		model.solver.add(assertion);
	}

	private MergePreconditionModel handleMergePrecondition(MergeMethodModel methodModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());
		Expr otherConst = model.ctx.mkFreshConst("s_other", classModel.getClassSort());
		var parser = new MergeMethodPreconditionExpressionParser(model, classModel, methodModel, thisConst, otherConst);
		Expr expr = parser.parseExpression(methodModel.getJmlPrecondition().orElse(null));
		expr = expr.simplify();

		for (var mergedField : parser.mergedFields) {
			ReplicatedClassModel mergeableClassModel = mergedField.classModel;

			var baseMergeableConstraints = model.getClassConstraints(mergedField.classModel.getBinding()).orElseThrow(
					() -> new IllegalStateException("constraints for class not found: " + mergeableClassModel )
			);

			if (!(baseMergeableConstraints instanceof ReplicatedClassConstraints))
				throw new IllegalStateException("constraints for mergebale class expected to be replicated constraints: " + mergeableClassModel);

			ReplicatedClassConstraints<?> mergeableConstraints = (ReplicatedClassConstraints<?>) baseMergeableConstraints;

			// Assumption: M is the underlying, mergeable class (e.g. a CRDT) and C is the current class (e.g. the bank account).
			// The field f is merged.
//			//Formula: forall s1 : C, s_m : M. post_merge_M(this.f, other.f, s_m) && s1.f == s_m => I_C(s1)
			var fieldDecls = classModel.getClassSort().getFieldDecls();
			Expr sm = model.ctx.mkFreshConst("s_m", mergeableClassModel.getClassSort());
			Expr s0 = model.ctx.mkFreshConst("s0", classModel.getClassSort());
			Expr s1 = model.ctx.mkFreshConst("s1", classModel.getClassSort());
			Expr result = model.ctx.mkForall(
					new Expr[] { sm, s0, s1 },
					model.ctx.mkImplies(
							model.ctx.mkAnd(
									getInvariant().apply(s0),
									mergeableConstraints.getInvariant().apply(sm),
									mergeableConstraints.getMergePostcondition().apply(mergedField.declaration.apply(thisConst), mergedField.declaration.apply(otherConst), sm),
									// TODO: s1 must equal a valid state s0 except for the field mergedField. (valid state s0 <=> I(s0))
									model.ctx.mkEq(mergedField.declaration.apply(s1), sm)
									),
							getInvariant().apply(s1)
					),
					1,
					null, null, null, null
			);

			expr = model.ctx.mkAnd(expr, result);

		}

		return constraintsFactory.makeMergePreconditionModel(thisConst, otherConst, expr);
	}

	private MergePostconditionModel handleMergePostcondition(MergeMethodModel methodModel) {
		Expr oldConst = model.ctx.mkFreshConst("s_old", classModel.getClassSort());
		Expr thisConst = model.ctx.mkFreshConst("s_new", classModel.getClassSort());
		Expr otherConst = model.ctx.mkFreshConst("s_other", classModel.getClassSort());

		var parser = new MergeMethodPostconditionExpressionParser(model, classModel, methodModel, thisConst, oldConst, otherConst);
		Expr expr = parser.parseExpression(methodModel.getJmlPostcondition().orElse(null));
		return constraintsFactory.makeMergePostconditionModel(oldConst, otherConst, thisConst, expr);
	}


	public MergePreconditionModel getMergePrecondition() {
		return mergePrecondition;
	}

	public MergePostconditionModel getMergePostcondition() {
		return mergePostcondition;
	}


	@Override
	public String toString() {
		return super.toString()
				+ "Merge Precondition ====\n" +  getMergePrecondition()  + "\n"
				+ "Merge Postcondition ====\n" +  getMergePostcondition();
	}



}
