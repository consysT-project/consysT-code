package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;

public class MethodPreconditionExpressionParser extends MethodExpressionParser {

	public MethodPreconditionExpressionParser(Context ctx, ClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(ctx, classModel, methodModel, thisConst);
	}
}
