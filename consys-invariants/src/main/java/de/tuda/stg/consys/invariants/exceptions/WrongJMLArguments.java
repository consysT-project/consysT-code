package de.tuda.stg.consys.invariants.exceptions;

import org.eclipse.jdt.internal.compiler.ast.Expression;

public class WrongJMLArguments extends RuntimeException {
	private final Expression expr;

	public WrongJMLArguments(Expression expr) {
		super("wrong arguments in expression: " + expr);
		this.expr = expr;
	}

	public Expression getExpr() {
		return expr;
	}
}
