package org.conloc.invariants.solver.subset.parser;

import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.exceptions.UnsupportedJMLExpression;
import org.conloc.invariants.solver.subset.model.BaseClassModel;
import org.conloc.invariants.solver.subset.model.ConstructorModel;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPreconditionExpressionParser extends MethodExpressionParser {

	public ConstructorPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, ConstructorModel constructorModel) {
		super(smt, classModel, constructorModel, null);
	}

	@Override
	protected Expr parseThisReference(ThisReference thisReference, int depth) {
		throw new UnsupportedJMLExpression(thisReference, "`this` cannot be referenced in constructor precondition");
	}

	@Override
	protected Expr parseJmlFieldReference(JmlFieldReference fieldReference, int depth) {
		throw new UnsupportedJMLExpression(fieldReference, "fields cannot be referenced in constructor precondition");
	}

	@Override
	public String toString() {
		return "ConstructorPreconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}

}
