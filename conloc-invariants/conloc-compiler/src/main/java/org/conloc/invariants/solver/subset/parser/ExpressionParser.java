package org.conloc.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.exceptions.UnsupportedJMLExpression;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.jmlspecs.jml4.ast.*;

/**
 * Super class of parsers for JML constraints.
 */
public abstract class ExpressionParser {

	// The z3 context used for creating expressions
	protected final ProgramModel model;

	protected ExpressionParser(ProgramModel model) {
		this.model = model;
	}

	public final Expr parseExpression(Expression expression) {
		return parseExpression(expression, 0);
	}

	protected final Expr parseExpression(Expression expression, int depth) {

		if (expression == null) {
//			Logger.warn("expression was null and was converted to `true`. Parser: " + this.toString());
			return model.ctx.mkTrue();
		}

		// literal expression: 10, -5.6, true, ...
		if (expression instanceof Literal) {
			return parseLiteral((Literal) expression, depth);
		}

		// one reference of a variable: "a"
		if (expression instanceof JmlSingleNameReference) {
			return parseJmlSingleReference((JmlSingleNameReference) expression, depth);
		}

		// "array[index]"
		if (expression instanceof JmlArrayReference) {
			return parseJmlArrayReference((JmlArrayReference) expression, depth);
		}

		if (expression instanceof ArrayAllocationExpression) {
			return parseArrayAllocationExpression((ArrayAllocationExpression) expression, depth);
		}

		// "({\forall | \exists | \sum} boundVarDeclarations; rangeExpression; body)"
		if (expression instanceof JmlQuantifiedExpression) {
			return parseJmlQuantifiedExpression((JmlQuantifiedExpression) expression, depth);
		}

		// expressions like BigInteger.ZERO
		if (expression instanceof JmlQualifiedNameReference) {
			return parseJmlQualifiedNameReference((JmlQualifiedNameReference) expression, depth);
		}

		// method calls
		if (expression instanceof JmlMessageSend) {
			return parseJmlMessageSend((JmlMessageSend) expression, depth);
		}

		if (expression instanceof ThisReference) {
			return parseThisReference((ThisReference) expression, depth);
		}

		if (expression instanceof JmlFieldReference) {
			return parseJmlFieldReference((JmlFieldReference) expression, depth);
		}

		// "\old(...)"
		if (expression instanceof JmlOldExpression) {
			return parseOldExpression((JmlOldExpression) expression, depth);
		}

		// \result is the result reference
		if (expression instanceof JmlResultReference) {
			return parseJmlResultReference((JmlResultReference) expression, depth);
		}

		// !a ...
		if (expression instanceof UnaryExpression) {
			return parseUnaryExpression((UnaryExpression) expression, depth);
		}

		// expressions like addition, modulo, and, or, ...
		if (expression instanceof BinaryExpression) {
			return parseBinaryExpression((BinaryExpression) expression, depth);
		}

		if (expression instanceof ConditionalExpression) {
			return parseConditionalExpression((ConditionalExpression) expression, depth);
		}

		if (expression instanceof CastExpression) {
			return parseCastExpression((CastExpression) expression, depth);
		}

		throw new UnsupportedJMLExpression(expression, "expression type not supported. depth: " + depth);
	}

	protected Expr parseConditionalExpression(ConditionalExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseBinaryExpression(BinaryExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseCastExpression(CastExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseUnaryExpression(UnaryExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlResultReference(JmlResultReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseOldExpression(JmlOldExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlFieldReference(JmlFieldReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseThisReference(ThisReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlMessageSend(JmlMessageSend expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseOperatorExpression(OperatorExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlQuantifiedExpression(JmlQuantifiedExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseArrayAllocationExpression(ArrayAllocationExpression expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlArrayReference(JmlArrayReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseLiteral(Literal expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}


	protected Expr parseJmlSingleReference(JmlSingleNameReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}

	protected Expr parseJmlQualifiedNameReference(JmlQualifiedNameReference expression, int depth) {
		throw new UnsupportedJMLExpression(expression);
	}


}
