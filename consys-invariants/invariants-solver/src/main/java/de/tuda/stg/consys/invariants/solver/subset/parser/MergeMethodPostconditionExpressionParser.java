package de.tuda.stg.consys.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.solver.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

public class MergeMethodPostconditionExpressionParser extends MethodPostconditionExpressionParser {


	public MergeMethodPostconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr oldConst, Expr otherConst) {
		super(smt, classModel, methodModel, thisConst, oldConst, null);
		addLocalVariable(methodModel.getArgument().binding, otherConst);
	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}

	@Override
	public String toString() {
		return "MergeMethodPostconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}



}
