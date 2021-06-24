package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.*;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPreconditionExpressionParser extends MethodExpressionParser {

	public ConstructorPreconditionExpressionParser(Context ctx, ClassModel classModel, ConstructorModel constructorModel) {
		super(ctx, classModel, constructorModel, null);
	}

	@Override
	public Expr parseThisReference(ThisReference thisReference) {
		// `this` cannot be referenced in constructor precondition.
		throw new WrongJMLArgumentsExpression(thisReference);
	}

	@Override
	public Expr parseJmlFieldReference(JmlFieldReference fieldReference) {
		// fields cannot be referenced in constructor precondition.
		throw new WrongJMLArgumentsExpression(fieldReference);
	}


}
