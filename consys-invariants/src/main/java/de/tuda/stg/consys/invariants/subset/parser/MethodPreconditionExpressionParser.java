package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;

public class MethodPreconditionExpressionParser extends MethodExpressionParser {

	public MethodPreconditionExpressionParser(Z3Binding smt, ClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(smt, classModel, methodModel, thisConst);
	}
}
