package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Maps;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Map;

public class ClassModel {

	private final Context ctx;
	private final ClassScope scope;

	private final InvariantModel invariant;

	private final Map<MethodDeclaration, PreconditionModel> preconditions;
	private final Map<MethodDeclaration, PostconditionModel> postconditions;

	public ClassModel(Context ctx, ClassScope scope) {
		this.ctx = ctx;
		this.scope = scope;

		JmlTypeDeclaration typ = scope.getJmlType();

		// Setup the invariant
		Expr invariantVar = ctx.mkFreshConst("s0", scope.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(ctx, scope, invariantVar);
		Expr invariantExpr = parser.parseExpression(typ.getInvariant());
		invariant = new InvariantModel(invariantVar, invariantExpr);

		// Setup the pre/postconditions
		preconditions = Maps.newHashMap();
		postconditions = Maps.newHashMap();

		Expr preconditionVar = ctx.mkFreshConst("s0", scope.getClassSort());
		for(MethodModel method : scope.getMethods()) {
			MethodExpressionParser methodPreParser = new MethodExpressionParser(ctx, scope, method, preconditionVar);
//			method.getMethod().getSpecification().getPrecondition()
		}

	}


	public InvariantModel getInvariant() {
		return invariant;
	}
}
