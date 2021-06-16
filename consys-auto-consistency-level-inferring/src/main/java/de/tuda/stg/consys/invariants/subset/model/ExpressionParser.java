package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalScope;
import org.eclipse.jdt.internal.compiler.ast.Expression;

public abstract class ExpressionParser {

	public Expr parseExpression(Expression expression) {
		throw new UnsupportedJMLExpression(expression);
	}
}
