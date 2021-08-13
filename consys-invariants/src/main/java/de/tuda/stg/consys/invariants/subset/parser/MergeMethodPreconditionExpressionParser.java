package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.jmlspecs.jml4.ast.JmlQualifiedNameReference;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;

public class MergeMethodPreconditionExpressionParser extends MethodExpressionParser {

	private final Expr otherConst;

	public MergeMethodPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr otherConst) {
		super(smt, classModel, methodModel, thisConst);
		this.otherConst = otherConst;
	}

	@Override
	protected Expr parseJmlSingleReference(JmlSingleNameReference jmlSingleNameReference, int depth) {
		Argument mergeArg = getMergeMethod().getArgument();

		if (jmlSingleNameReference.binding.equals(mergeArg.binding)) {
			return otherConst;
		}

		return super.parseJmlSingleReference(jmlSingleNameReference, depth);
	}

//	@Override
//	protected Expr parseJmlQualifiedNameReference(JmlQualifiedNameReference jmlQualifiedNameReference, int depth) {
//		Argument mergeArg = getMergeMethod().getArgument();
//
//		if (jmlQualifiedNameReference.binding.equals(mergeArg.binding)) {
//			FieldBinding fieldBinding = jmlQualifiedNameReference.otherBindings[0];
//
//			return getClassModel().getField(fieldBinding)
//					.map(field -> field.getAccessor().apply(otherConst))
//					.orElseThrow(() -> new UnsupportedJMLExpression(jmlQualifiedNameReference));
//		}
//
//		return super.parseJmlQualifiedNameReference(jmlQualifiedNameReference, depth);
//	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}
}
