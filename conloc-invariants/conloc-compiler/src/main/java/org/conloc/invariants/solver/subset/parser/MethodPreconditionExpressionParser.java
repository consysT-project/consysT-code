package org.conloc.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.subset.model.AbstractMethodModel;
import org.conloc.invariants.solver.subset.model.BaseClassModel;
import org.conloc.invariants.solver.subset.model.ProgramModel;

public class MethodPreconditionExpressionParser extends MethodExpressionParser {

	public MethodPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(smt, classModel, methodModel, thisConst);
	}

	@Override
	public String toString() {
		return "MethodPreconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}
}
