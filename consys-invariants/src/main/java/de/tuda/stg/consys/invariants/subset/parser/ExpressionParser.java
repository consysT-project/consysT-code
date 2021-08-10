package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;

/**
 * Super class of parsers for JML constraints.
 */
public abstract class ExpressionParser {

	public final Expr parseExpression(Expression expression) {
		return parseExpression(expression, 0);
	}

	protected Expr parseExpression(Expression expression, int depth) {
		throw new UnsupportedJMLExpression(expression, "expression type not supported. depth: " + depth);
	}
}
