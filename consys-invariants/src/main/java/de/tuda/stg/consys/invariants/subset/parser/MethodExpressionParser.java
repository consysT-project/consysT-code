package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ArgumentModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

/**
 * Parser for parsing expression inside of methods.
 */
public class MethodExpressionParser extends ClassExpressionParser {

	protected final AbstractMethodModel<?> methodModel;

	public MethodExpressionParser(Z3Binding smt, ClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst) {
		super(smt, classModel, thisConst);
		this.methodModel = methodModel;
	}

	@Override
	public Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference) {
		return methodModel.getArgument(jmlSingleNameReference)
				.flatMap(ArgumentModel::getConst)
				.orElseGet(() -> super.parseJmlSingleReference(jmlSingleNameReference));
	}
}
