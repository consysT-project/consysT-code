package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.ConstructorModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPostconditionExpressionParser extends MethodExpressionParser {

	public ConstructorPostconditionExpressionParser(Z3Binding smt, ClassModel classModel, ConstructorModel constructorModel, Expr thisConst) {
		super(smt, classModel, constructorModel, thisConst);
	}

}
