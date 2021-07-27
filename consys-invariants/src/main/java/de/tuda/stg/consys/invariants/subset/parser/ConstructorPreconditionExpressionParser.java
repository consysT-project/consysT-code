package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArguments;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.ConstructorModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPreconditionExpressionParser extends MethodExpressionParser {

	public ConstructorPreconditionExpressionParser(ProgramModel smt, ClassModel classModel, ConstructorModel constructorModel) {
		super(smt, classModel, constructorModel, null);
	}

	@Override
	public Expr parseThisReference(ThisReference thisReference) {
		// `this` cannot be referenced in constructor precondition.
		throw new WrongJMLArguments(thisReference);
	}

	@Override
	public Expr parseJmlFieldReference(JmlFieldReference fieldReference) {
		// fields cannot be referenced in constructor precondition.
		throw new WrongJMLArguments(fieldReference);
	}


}
