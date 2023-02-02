package org.conloc.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.subset.model.BaseClassModel;
import org.conloc.invariants.solver.subset.model.ConstructorModel;
import org.conloc.invariants.solver.subset.model.ProgramModel;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPostconditionExpressionParser extends MethodExpressionParser {

	public ConstructorPostconditionExpressionParser(ProgramModel model, BaseClassModel classModel, ConstructorModel constructorModel, Expr thisConst) {
		super(model, classModel, constructorModel, thisConst);
	}

	@Override
	public String toString() {
		return "ConstructorPostconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}

}
