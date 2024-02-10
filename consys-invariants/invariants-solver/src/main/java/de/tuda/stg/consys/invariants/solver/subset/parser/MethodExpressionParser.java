package de.tuda.stg.consys.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.solver.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.logging.Logger;

/**
 * Parser for parsing expression inside of methods.
 */
public class MethodExpressionParser extends ClassExpressionParser {

	protected final AbstractMethodModel<?> methodModel;

	public MethodExpressionParser(ProgramModel smt, BaseClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(smt, classModel, thisConst);
		this.methodModel = methodModel;

		for (var arg : methodModel.getArguments()) {
			arg.getConst().ifPresentOrElse(
					expr -> addLocalVariable(arg.getBinding(), expr),
					() -> Logger.warn("argument not available in constraints: " + arg)
			);
		}
	}

	@Override
	public String toString() {
		return "MethodExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}
}
