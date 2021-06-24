package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.*;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class ConstructorExpressionParser extends ClassExpressionParser {

	protected final ConstructorModel constructorModel;

	/**
	 * @param ctx
	 * @param classModel
	 * @param thisConst  Substitute all `this` references with the given const. The const needs to have
	 */
	public ConstructorExpressionParser(Context ctx, ClassModel classModel, ConstructorModel constructorModel, Expr thisConst) {
		super(ctx, classModel, thisConst);
		this.constructorModel = constructorModel;
	}

	@Override
	public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
		return constructorModel.getArgument(jmlSingleNameReference)
				.map(ArgumentModel::getConst)
				.orElseGet(() -> super.parseJmlSingleReference(jmlSingleNameReference));
	}
}
