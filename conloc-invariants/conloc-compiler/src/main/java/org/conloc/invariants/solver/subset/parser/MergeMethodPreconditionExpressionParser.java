package org.conloc.invariants.solver.subset.parser;

import com.google.common.collect.Sets;
import com.microsoft.z3.Expr;
import org.conloc.invariants.solver.exceptions.UnsupportedJMLExpression;
import org.conloc.invariants.solver.subset.model.BaseClassModel;
import org.conloc.invariants.solver.subset.model.MergeMethodModel;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.conloc.invariants.solver.subset.model.ReplicatedClassModel;
import org.conloc.invariants.solver.subset.utils.JDTUtils;
import org.conloc.invariants.solver.subset.utils.Z3SubstitutionFunction1;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlMessageSend;

import java.util.Set;

public class MergeMethodPreconditionExpressionParser extends MethodExpressionParser {

	/** A set of fields that are merged by this merge method. */
	public Set<MergeDeclaration> mergedFields = Sets.newHashSet();

	public MergeMethodPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr otherConst) {
		super(smt, classModel, methodModel, thisConst);
		addLocalVariable(methodModel.getArgument().binding, otherConst);
	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}

	public Expr getOtherConst() {
		return lookupLocalVariable(getMergeMethod().getArgument().binding).orElseThrow(
				() -> new IllegalStateException("local variable for merge parameter not initialized"));
	}

	@Override
	protected Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend, int depth) {
		var methodBinding = jmlMessageSend.binding;

		/* resolve stateful methods */
		if (JDTUtils.methodMatchesSignature(jmlMessageSend.actualReceiverType, methodBinding, true, "org.conloc.invariants.utils.InvariantUtils", "__merge", "java.lang.Object")) {
			if (!model.config.MODEL__INCLUDE_IMPURE_METHODS) {
				throw new UnsupportedJMLExpression(jmlMessageSend, "merge only usable when include_impure_methods is true in config");
			}

			// In the case of the call: merge(...)
			//Comments by example merge(this.f)

			/* Find the class model of this.f. this.f has to be a class that supports merging.*/
			TypeBinding argType = jmlMessageSend.arguments[0].resolvedType;
			if (!(argType instanceof ReferenceBinding))
				throw new UnsupportedJMLExpression(jmlMessageSend, "type of merge parameter is not a reference, but was: " + argType);
			BaseClassModel mergedClassModel = model.getClassModel((ReferenceBinding) argType)
					.orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend, "merge parameter does not reference a class in the model, but was: " + argType));

			if (!(mergedClassModel instanceof ReplicatedClassModel))
				throw new UnsupportedJMLExpression(jmlMessageSend, "merge parameter does not refernce a mergeable data type, but was: " + mergedClassModel);
			ReplicatedClassModel replicatedClassModel = (ReplicatedClassModel) mergedClassModel;

			// thisMergable is the z3 expr for this.f
			Expr thisMergeable = parseExpression(jmlMessageSend.arguments[0]);

			// Add the merge to the merges
			mergedFields.add( new MergeDeclaration(
					new Z3SubstitutionFunction1("merge", getThisConst(), thisMergeable),
					replicatedClassModel)
			);

			// The merge condition just evaluates to true. The mergedFields are resolved in the constraint builder.
			return model.ctx.mkTrue();

//			if (jmlMessageSend.arguments[0] instanceof JmlMessageSend) {
//				var mergeMethod = (JmlMessageSend) jmlMessageSend.arguments[0];
//				var receiverExpr = parseExpression(statefulMethod.receiver);
//
//				return withThisReference(oldConst, () -> withStatefulMethods(() -> {
//					var statefulMethodExpr = parseExpression(statefulMethod, 0);
//					var result = model.ctx.mkEq(
//							receiverExpr,
//							statefulMethodExpr
//					);
//
//					return result;
//				}));
//			} else {
//				throw new UnsupportedJMLExpression(jmlMessageSend, "expected method call in stateful");
//			}


		}

		return super.parseJmlMessageSend(jmlMessageSend, depth);
	}

	@Override
	public String toString() {
		return "MergeMethodPreconditionExpressionParser{" +
				"methodModel=" + methodModel +
				'}';
	}


	public static class MergeDeclaration {
		public final Z3SubstitutionFunction1 declaration;
		public final ReplicatedClassModel classModel;

		public MergeDeclaration(Z3SubstitutionFunction1 declaration, ReplicatedClassModel classModel) {
			this.declaration = declaration;
			this.classModel = classModel;
		}
	}

}
