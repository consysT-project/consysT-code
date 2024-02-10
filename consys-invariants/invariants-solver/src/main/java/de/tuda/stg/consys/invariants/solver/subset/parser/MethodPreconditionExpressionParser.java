package de.tuda.stg.consys.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.solver.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

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
