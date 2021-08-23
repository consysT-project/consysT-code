package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class MergeMethodPreconditionExpressionParser extends MethodExpressionParser {

	public MergeMethodPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr otherConst) {
		super(smt, classModel, methodModel, thisConst);

		addLocalVariable(methodModel.getArgument().binding, otherConst);
	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}

	@Override
	public String toString() {
		return "MergeMethodPreconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}
}
