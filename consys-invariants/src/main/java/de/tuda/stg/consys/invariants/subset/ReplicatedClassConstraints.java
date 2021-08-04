package de.tuda.stg.consys.invariants.subset;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.*;
import de.tuda.stg.consys.invariants.subset.parser.*;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate2;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate3;
import org.jmlspecs.jml4.ast.JmlMethodSpecification;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

public class ReplicatedClassConstraints<CModel extends ReplicatedClassModel> extends ClassConstraints<CModel> {

	/** Merge precondtion */
	private final MergePreconditionModel mergePrecondition;
	/** Merge postcondition */
	private final MergePostconditionModel mergePostcondition;


	/* Helper classes for predicate models. */
	public static class MergePreconditionModel extends Z3Predicate2 {
		MergePreconditionModel(Expr thisConst, Expr otherConst, Expr body) {
			super("pre_merge", thisConst, otherConst, body);
		}
	}

	public static class MergePostconditionModel extends Z3Predicate3 {
		MergePostconditionModel(Expr oldConst, Expr otherConst, Expr thisConst, Expr body) {
			super("post_merge", oldConst, otherConst, thisConst, body);
		}
	}



	public ReplicatedClassConstraints(ProgramModel model, CModel classModel) {
		super(model, classModel);

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the merge pre/postcondition.
		MergeMethodModel mergeModel = classModel.getMergeMethod();
		mergePrecondition = handleMergePrecondition(mergeModel);
		mergePostcondition = handleMergePostcondition(mergeModel);

	}

	private MergePreconditionModel handleMergePrecondition(MergeMethodModel methodModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());
		Expr otherConst = model.ctx.mkFreshConst("s_other", classModel.getClassSort());
		var parser = new MergeMethodPreconditionExpressionParser(model, classModel, methodModel, thisConst, otherConst);
		Expr expr = parser.parseExpression(methodModel.getJPrecondition().orElse(null));
		return new MergePreconditionModel(thisConst, otherConst, expr);
	}

	private MergePostconditionModel handleMergePostcondition(MergeMethodModel methodModel) {
		Expr oldConst = model.ctx.mkFreshConst("s_old", classModel.getClassSort());
		Expr thisConst = model.ctx.mkFreshConst("s_new", classModel.getClassSort());
		Expr otherConst = model.ctx.mkFreshConst("s_other", classModel.getClassSort());

		var parser = new MergeMethodPostconditionExpressionParser(model, classModel, methodModel, thisConst, oldConst, otherConst);
		Expr expr = parser.parseExpression(methodModel.getJPostcondition().orElse(null));
		return new MergePostconditionModel(oldConst, otherConst, thisConst, expr);
	}


	public MergePreconditionModel getMergePrecondition() {
		return mergePrecondition;
	}

	public MergePostconditionModel getMergePostcondition() {
		return mergePostcondition;
	}



//	private Expr getForallInvariant(InvariantModel inv) {
//		var forallVar = model.ctx.mkFreshConst("s_inv", classModel.getClassSort());
//		model.ctx.mkForall(
//				new Expr[] {forallVar},
//				model.ctx.mkTrue(),
//
//
//		)
//	}

	@Override
	public String toString() {
		return super.toString()
				+ "Merge Precondition ====\n" +  getMergePrecondition()  + "\n"
				+ "Merge Postcondition ====\n" +  getMergePostcondition();
	}



}
