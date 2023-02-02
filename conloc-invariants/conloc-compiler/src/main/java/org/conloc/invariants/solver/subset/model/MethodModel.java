package org.conloc.invariants.solver.subset.model;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import org.conloc.invariants.solver.subset.model.types.TypeModel;
import org.conloc.invariants.solver.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	// f(thisState, args...) => (newState, return)
	FuncDecl<?> funcState;
	FuncDecl<?> funcValue;

	public MethodModel(ProgramModel model, BaseClassModel clazz, JmlMethodDeclaration method) {
		this(model, clazz, method, true);
	}

	MethodModel(ProgramModel model, BaseClassModel clazz, JmlMethodDeclaration method, boolean tryInitialize) {
		super(model, clazz, method);

		var argTypes = getArgumentTypes();
		var retType = getReturnType();

		if (tryInitialize && argTypes.stream().allMatch(TypeModel::hasSort) && retType.hasSort() /* && isPure() && !hasPrecondition() */) {
			var decls = initializeMethod(model, clazz, method, argTypes, retType);
			funcState = decls[0];
			funcValue = decls[1];
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
//				Logger.warn("jml spec case not supported. Method: " + this + ". Spec case: "  + rest);
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
			return true;
		}
		// The assignable clause is \nothing.
		return maybeClause.get().expr.equals(JmlKeywordExpression.NOTHING);
	}

	public boolean hasPrecondition() {
		var maybePrecond = getJmlPrecondition();
		return maybePrecond.isPresent() && maybePrecond.stream().noneMatch(cond -> cond instanceof TrueLiteral);
	}

	public boolean usableAsConstraint() {
		return funcValue != null && funcState != null && (model.config.MODEL__INCLUDE_IMPURE_METHODS || isPure());
	}
}
