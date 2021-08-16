package de.tuda.stg.consys.invariants.subset.parser;

import com.google.common.collect.Lists;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.model.AbstractMethodModel;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.FieldModel;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.jmlspecs.jml4.ast.*;

import java.util.List;

public class MethodPostconditionExpressionParser extends MethodExpressionParser {

	private Expr oldConst;
	private Expr resultConst; // Can be null, if method has no result.

	public MethodPostconditionExpressionParser(ProgramModel smt, BaseClassModel classModel, AbstractMethodModel<?> methodModel, Expr thisConst, Expr oldConst, Expr resultConst) {
		super(smt, classModel, methodModel, thisConst);

		this.oldConst = oldConst;
		this.resultConst = resultConst;
	}

	@Override
	protected Expr parseOldExpression(JmlOldExpression jmlOldExpression, int depth) {
		// Change the resolution of `this` to the const for old.
		return withThisReference(oldConst, () -> parseExpression(jmlOldExpression.expression, depth + 1));
	}

	@Override
	protected Expr parseJmlResultReference(JmlResultReference jmlResultReference, int depth) {
		if (resultConst == null || methodModel.returnsVoid())
			throw new UnsupportedJMLExpression(jmlResultReference, "\\result can not be used when method does return void.");

		return resultConst;
	}

	@Override
	protected Expr parseJmlMessageSend(JmlMessageSend jmlMessageSend, int depth) {
		var methodBinding = jmlMessageSend.binding;

		/* resolve stateful methods */
		if (JDTUtils.methodMatchesSignature(methodBinding, true, "de.tuda.stg.consys.utils.InvariantUtils", "stateful", "java.lang.Object")) {
			if (jmlMessageSend.arguments[0] instanceof JmlMessageSend) {
				var statefulMethod = (JmlMessageSend) jmlMessageSend.arguments[0];
				var receiverExpr = parseExpression(statefulMethod.receiver);

				return withThisReference(oldConst, () -> withStatefulMethods(() -> {
					var statefulMethodExpr = parseExpression(statefulMethod, 0);
					var result = model.ctx.mkEq(
							receiverExpr,
							statefulMethodExpr
					);

					return result;
				}));
			} else {
				throw new UnsupportedJMLExpression(jmlMessageSend, "expected method call in stateful");
			}
		}

		return super.parseJmlMessageSend(jmlMessageSend, depth);
	}



	/**
	 * This visit method translates an assignable clause into a postcondition. {@code assignable
	 * \nothing} translates to setting all prestate constants equal to the poststate constants. {@code
	 * assignable a} does the same but leaves {@code a} out, also {@code assignable a[3]} but for
	 * a[3].
	 *
	 * @return the created postcondition from the assignable clause
	 */
	public BoolExpr parseJmlAssignableClause(JmlAssignableClause jmlAssignableClause) {

		if (jmlAssignableClause == null || jmlAssignableClause.expr.equals(JmlKeywordExpression.NOTHING)) {
			// assignable \nothing ==> \old(this) == this
			return model.ctx.mkEq(oldConst, getThisConst());
		} else if (jmlAssignableClause.expr instanceof JmlStoreRefListExpression) {
			// assignable (a | a[n])

			// collect all java variable references from the assignable clause
			Expression[] references = ((JmlStoreRefListExpression) jmlAssignableClause.expr).exprList;
			BoolExpr result = model.ctx.mkTrue();

			// collect all names of the variables that are mentioned
			for (FieldModel field : getClassModel().getFields()) {

				if (field.isArray()) {
					// Handle array assignments
					boolean allIndicesAssigned = false;
					List<Expr> assignedIndices = Lists.newLinkedList();

					for (Expression expr : references) {
						if (expr instanceof NameReference) {
							Reference ref = (Reference) expr;

							// Check that ref references a field.
							if (ref.fieldBinding() == null) {
								throw new UnsupportedJMLExpression(ref);
							}

							// Check whether the binding references field.
							if (ref.fieldBinding().equals(field.getBinding())) {
								// The binding is assigned. We cannot make any assertions on that field.
								allIndicesAssigned = true;
								break;
							}
						} else if (expr instanceof JmlArrayRangeStoreRef) {
							// TODO: How to handle array ranges, e.g., a[*]?
//							var arrayExpr = ((JmlArrayRangeStoreRef) expr).delegate; //<- this thing is private

							throw new UnsupportedJMLExpression(expr);
						} else if (expr instanceof JmlArrayReference) {
							JmlArrayReference arrayRef = (JmlArrayReference) expr;

							if (arrayRef.receiver instanceof NameReference) {
								Reference receiver = (Reference) arrayRef.receiver;

								// Array does not reference a field
								if (receiver.fieldBinding() == null) {
									throw new UnsupportedJMLExpression(arrayRef);
								}

								if (receiver.fieldBinding().equals(field.getBinding())) {
									Expr index = parseExpression(arrayRef.position, 0);
									assignedIndices.add(index);
								}
							}
						}
					}

					if (allIndicesAssigned) {
						// Do nothing. We can not add any assertions.
					} else if (!assignedIndices.isEmpty()) {
						// Only some indices are assigned.

						// index of the forall expression
						Expr forIndex = model.ctx.mkFreshConst("i", model.ctx.getIntSort());

						// i != index1, i != index2, ...
						Expr[] assignmentExprs = assignedIndices.stream()
								.map(index -> model.ctx.mkNot(model.ctx.mkEq(forIndex, index)))
								.toArray(length -> new Expr[length]);

						//(i != index1 & i != index2) => arr[i] == \old(arr[i])
						Expr forBody = model.ctx.mkImplies(
								model.ctx.mkAnd(assignmentExprs),
								model.ctx.mkEq(
										model.ctx.mkSelect(field.getAccessor().apply(getThisConst()), forIndex),
										model.ctx.mkSelect(field.getAccessor().apply(oldConst), forIndex)
								)
						);

						Expr forall = model.ctx.mkForall(new Expr[] {forIndex}, forBody, 1, null, null, null, null);
						result = model.ctx.mkAnd(result, forall);

					} else if (!allIndicesAssigned) {
						//if the field is not assigned then we add an equality expression.
						result = model.ctx.mkAnd(result, model.ctx.mkEq(
								field.getAccessor().apply(oldConst),
								field.getAccessor().apply(getThisConst()))
						);
					}

				} else {
					// Handle single assignments
					boolean isAssigned = false;

					for (Expression ref : references) {
						if (ref instanceof JmlSingleNameReference) {
							Binding b = ((JmlSingleNameReference) ref).binding;
							if (b.equals(field.getBinding())) {
								// The binding is assigned. We cannot make any assertions on that field.
								isAssigned = true;
								break;
							}
						}
					}

					if (!isAssigned) {
						//if the field is not assigned then we add an equality expression.
						result = model.ctx.mkAnd(result, model.ctx.mkEq(
								field.getAccessor().apply(oldConst),
								field.getAccessor().apply(getThisConst()))
						);
					}
				}
			}
			return result;
		}

		throw new IllegalArgumentException(jmlAssignableClause.toString());
	}
}
