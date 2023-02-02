package org.conloc.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.subset.model.BaseClassModel;
import org.conloc.invariants.solver.subset.model.MergeMethodModel;
import org.conloc.invariants.solver.subset.model.ProgramModel;

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
