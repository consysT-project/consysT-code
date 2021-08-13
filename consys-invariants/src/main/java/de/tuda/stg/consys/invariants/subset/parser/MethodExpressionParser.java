package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ArgumentModel;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class MethodExpressionParser extends ClassExpressionParser {

	protected final AbstractMethodModel<?> methodModel;

	public MethodExpressionParser(ProgramModel smt, BaseClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(smt, classModel, thisConst);
		this.methodModel = methodModel;
	}

	@Override
	protected Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference, int depth) {
		return methodModel.getArgument(jmlSingleNameReference)
				.flatMap(ArgumentModel::getConst)
				.orElseGet(() -> super.parseJmlSingleReference(jmlSingleNameReference, depth));
	}
}
