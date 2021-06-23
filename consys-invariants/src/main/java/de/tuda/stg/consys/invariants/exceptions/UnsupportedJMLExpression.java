package de.tuda.stg.consys.invariants.exceptions;

import org.eclipse.jdt.internal.compiler.ast.Expression;

public class UnsupportedJMLExpression extends RuntimeException {
	private final Expression expr;

	public UnsupportedJMLExpression(Expression expr) {
		super("unsupported expression: " + expr + " (of class " + expr.getClass() + ")");
		this.expr = expr;
	}

	public Expression getExpr() {
		return expr;
	}
}
