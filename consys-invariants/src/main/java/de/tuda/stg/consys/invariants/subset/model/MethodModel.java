package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	// f(thisState, args...) => (newState, return)
	private final FuncDecl<?> funcState;
	private final FuncDecl<?> funcValue;

	public MethodModel(ProgramModel model, BaseClassModel clazz, JmlMethodDeclaration method) {
		super(model, clazz, method);

		var argTypes = getArgumentTypes();
		var retType = getReturnType();

		if (argTypes.stream().allMatch(TypeModel::hasSort) && retType.hasSort() /* && isPure() && !hasPrecondition() */) {
			// Add `this` and `\old this` to the arguments of the z3 function.
			var argSorts = argTypes.stream().map(TypeModel::toSort).toArray(Sort[]::new);
			var argSortsAndThis = Z3Utils.arrayPrepend(Sort[]::new, argSorts, clazz.getClassSort());

			funcState = model.ctx.mkFreshFuncDecl(getName() + "_state", argSortsAndThis, clazz.getClassSort());
			funcValue = model.ctx.mkFreshFuncDecl(getName() + "_value", argSortsAndThis, retType.toSort());

		} else {
			funcState = null;
			funcValue = null;
		}
	}

	private Optional<FuncDecl<?>> toFuncDeclState() {
		if (!usableAsConstraint()) return Optional.empty();
		return Optional.ofNullable(funcState);
	}

	private Optional<FuncDecl<?>> toFuncDeclValue() {
		if (!usableAsConstraint()) return Optional.empty();
		return Optional.ofNullable(funcValue);
	}

	public Optional<Expr> makeApplyReturnValue(Expr thisExpr, Expr[] argExprs) {
		return toFuncDeclValue().map(funcDecl ->
				model.ctx.mkApp(funcDecl, Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisExpr))
		);
	}

	public Optional<Expr> makeApplyReturnState(Expr thisExpr, Expr[] argExprs) {
		return toFuncDeclState().map(funcDecl ->
				model.ctx.mkApp(funcDecl, Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisExpr))
		);
	}



	public Optional<JmlAssignableClause> getAssignableClause() {
		JmlAssignableClause result = null;

		// If there is no JML specification
		if (method.getSpecification() == null) {
			return Optional.empty();
		}

		for (JmlSpecCase jmlSpecCase : method.getSpecification().getSpecCases()) {
			var rest = jmlSpecCase.body.rest;

			if (rest instanceof JmlSpecCaseRestAsClauseSeq) {
				for (JmlClause clause : ((JmlSpecCaseRestAsClauseSeq) rest).clauses) {
					if (clause instanceof JmlAssignableClause) {
						if (result != null) {
							throw new IllegalStateException("multiple assignable clauses: " + clause);
						}
						result = (JmlAssignableClause) clause;
					}
				}
			} else {
				Logger.warn("jml spec case not supported: " + rest);
				return Optional.empty();
			}
		}

		return Optional.ofNullable(result);
	}

	/** Checks whether the method has an @assignable \nothing clause */
	public boolean isPure() {
		var maybeClause = getAssignableClause();
		if (maybeClause.isEmpty()) {
			// There is no assignable clause, so we have to assume that the method is not pure.
			return false;
		}
		// The assignable clause is \nothing.
		return maybeClause.get().expr.equals(JmlKeywordExpression.NOTHING);
	}

	public boolean hasPrecondition() {
		var maybePrecond = getJmlPrecondition();
		return maybePrecond.isPresent() && !maybePrecond.stream().anyMatch(cond -> cond instanceof TrueLiteral);
	}

	public boolean usableAsConstraint() {
		return funcValue != null && funcState != null && (model.config.MODEL__INCLUDE_IMPURE_METHODS || isPure());
	}
}
