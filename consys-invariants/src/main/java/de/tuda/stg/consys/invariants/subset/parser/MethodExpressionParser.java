package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ArgumentModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;
import de.tuda.stg.consys.invariants.subset.z3_model.InternalScope;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class MethodExpressionParser extends ClassExpressionParser {

	protected final AbstractMethodModel<?> methodModel;

	/**
	 * @param ctx
	 * @param classModel
	 * @param thisConst  Substitute all `this` references with the given const. The const needs to have
	 */
	public MethodExpressionParser(Context ctx, ClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(ctx, classModel, thisConst);
		this.methodModel = methodModel;
	}

	@Override
	public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
		return methodModel.getArgument(jmlSingleNameReference)
				.map(ArgumentModel::getConst)
				.orElseGet(() -> super.parseJmlSingleReference(jmlSingleNameReference));
	}
}
