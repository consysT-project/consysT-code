package de.tuda.stg.consys.invariants.exceptions;

import org.eclipse.jdt.internal.compiler.ast.Expression;

public class WrongJMLArgumentsExpression extends RuntimeException {
	private final Expression expr;

	public WrongJMLArgumentsExpression(Expression expr) {
		super("wrong arguments in expression: " + expr);
		this.expr = expr;
	}

	public Expression getExpr() {
		return expr;
	}
}
