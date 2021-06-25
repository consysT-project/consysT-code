package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;

/**
 * Super class of parsers for JML constraints.
 */
public abstract class ExpressionParser {

	public Expr parseExpression(Expression expression) {
		throw new UnsupportedJMLExpression(expression);
	}
}
