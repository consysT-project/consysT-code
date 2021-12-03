package de.tuda.stg.consys.invariants.subset.parser;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.MergeMethodModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.model.ReplicatedClassModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlMessageSend;
import scala.NotImplementedError;

public class MergeMethodPreconditionExpressionParser extends MethodExpressionParser {

	public MergeMethodPreconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, MergeMethodModel methodModel, Expr thisConst, Expr otherConst) {
		super(smt, classModel, methodModel, thisConst);
		addLocalVariable(methodModel.getArgument().binding, otherConst);
	}

	public MergeMethodModel getMergeMethod() {
		return (MergeMethodModel) methodModel;
	}

	@Override
	protected Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend, int depth) {
		var methodBinding = jmlMessageSend.binding;

		/* resolve stateful methods */
		if (JDTUtils.methodMatchesSignature(jmlMessageSend.actualReceiverType, methodBinding, true, "de.tuda.stg.consys.utils.InvariantUtils", "__merge", "java.lang.Object")) {
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

			// Find the merge declaration of this.f
			MergeMethodModel underlyingMergeMethod = replicatedClassModel.getMergeMethod();

			// thisMergable is the z3 expr for this.f
			Expr thisMergeable = parseExpression(jmlMessageSend.arguments[0]);
			//otherMErgeable is the z3 expr for other.f
			Expr otherVar = lookupLocalVariable(getMergeMethod().getArgument().binding).orElseThrow(
					() -> new IllegalStateException("local variable for merge parameter not initialized"));
			Expr otherMergeable = withThisReference(otherVar, () -> parseExpression(jmlMessageSend.arguments[0]));

			// Create expression that merges this.f and other.f
			Expr underylingMerge = underlyingMergeMethod.makeApplyReturnState(
					thisMergeable, new Expr[] { otherMergeable }
			).orElseThrow(() -> new UnsupportedJMLExpression(jmlMessageSend, "can not apply merge function of " + underlyingMergeMethod));

			//TODO: forall s. merge(this.f, other.f) == s => I(s)
			//TODO: Move to Constraints?
			return underylingMerge;

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


}
