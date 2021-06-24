package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.WrongJMLArgumentsExpression;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.ConstructorModel;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.jmlspecs.jml4.ast.JmlFieldReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorPostconditionExpressionParser extends MethodExpressionParser {

	/**
	 * @param ctx
	 * @param classModel
	 * @param thisConst  Substitute all `this` references with the given const. The const needs to have
	 */
	public ConstructorPostconditionExpressionParser(Context ctx, ClassModel classModel, ConstructorModel constructorModel, Expr thisConst) {
		super(ctx, classModel, constructorModel, thisConst);
	}

}
