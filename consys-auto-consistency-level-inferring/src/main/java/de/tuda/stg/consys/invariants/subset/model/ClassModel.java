package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

public class ClassModel {

	private final Context ctx;
	private final ClassScope scope;

	private final InvariantModel invariant;

	public ClassModel(Context ctx, ClassScope scope) {
		this.ctx = ctx;
		this.scope = scope;

		// Setup the invariant
		Expr invariantVar = ctx.mkConst("s0", scope.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(ctx, scope, invariantVar);
		Expr invariantExpr = parser.parseExpression(scope.getJmlType().getInvariant());
		invariant = new InvariantModel(invariantVar, invariantExpr);
	}


	public InvariantModel getInvariant() {
		return invariant;
	}
}
