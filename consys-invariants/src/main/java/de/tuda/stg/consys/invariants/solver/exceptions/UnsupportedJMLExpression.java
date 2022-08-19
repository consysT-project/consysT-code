package de.tuda.stg.consys.invariants.solver.exceptions;

import org.eclipse.jdt.internal.compiler.ast.Expression;

public class UnsupportedJMLExpression extends RuntimeException {
	private final Expression expr;

	public UnsupportedJMLExpression(Expression expr, String reason) {
		super(expr + " (of type " + expr.getClass().getSimpleName() + ") at [" + expr.sourceStart + "-" + expr.sourceEnd+ "]."
				+ (reason == null ? "" : " Reason: " + reason + "."));
		this.expr = expr;
	}

	public UnsupportedJMLExpression(Expression expr) {
		this(expr, null);
	}

	public Expression getExpr() {
		return expr;
	}
}
