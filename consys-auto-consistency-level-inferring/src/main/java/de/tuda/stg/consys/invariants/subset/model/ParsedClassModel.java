package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Maps;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.parser.ClassExpressionParser;
import de.tuda.stg.consys.invariants.subset.parser.MethodPreconditionExpressionParser;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Map;
import java.util.stream.Collectors;

public class ParsedClassModel {

	private final Context ctx;
	private final ClassModel scope;

	private final InvariantModel invariant;

	private final Map<MethodBinding, PreconditionModel> preconditions;
	private final Map<MethodBinding, PostconditionModel> postconditions;

	public ParsedClassModel(Context ctx, ClassModel scope) {
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

		for(MethodModel method : scope.getMethods()) {
			Expr preconditionVar = ctx.mkFreshConst("s0", scope.getClassSort());
			MethodPreconditionExpressionParser methodPreParser = new MethodPreconditionExpressionParser(ctx, scope, method, preconditionVar);
			Expr preconditionExpr = methodPreParser.parseExpression(method.getMethod().getSpecification().getPrecondition());
			preconditions.put(method.getMethod().binding, new PreconditionModel(preconditionVar, preconditionExpr));
		}

	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public PreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	@Override
	public String toString() {
		return "Class" + scope.getClassName() + "====\n"
				+ "Invariant ====\n" + getInvariant() + "\n"
				+ "Preconditions ====\n" + preconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining());
	}
}
