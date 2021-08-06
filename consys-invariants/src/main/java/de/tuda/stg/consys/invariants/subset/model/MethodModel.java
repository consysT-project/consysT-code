package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	// f(thisState, args...) => (newState, return)
	private final FuncDecl<?> func;
	private final TupleSort returnSort;

	public MethodModel(ProgramModel model, BaseClassModel clazz, JmlMethodDeclaration method) {
		super(model, clazz, method);

		var argTypes = getArgumentTypes();
		var retType = getReturnType();

		if (argTypes.stream().allMatch(TypeModel::hasSort) && retType.hasSort() /* && isPure() && !hasPrecondition() */) {
			// Add `this` and `\old this` to the arguments of the z3 function.
			var argSorts = argTypes.stream().map(TypeModel::toSort).toArray(Sort[]::new);
			var argSortsAndThis = Z3Utils.arrayPrepend(Sort[]::new, argSorts, clazz.getClassSort());

			returnSort = model.ctx.mkTupleSort(
					model.ctx.mkSymbol("T_RET_" + getName()),
					new Symbol[] { model.ctx.mkSymbol("get_state"), model.ctx.mkSymbol("get_result") },
					new Sort[] { clazz.getClassSort(), retType.toSort() }
			);

			func = model.ctx.mkFreshFuncDecl(getName(), argSortsAndThis, returnSort);
		} else {
			func = null;
			returnSort = null;
		}
	}

	private Optional<FuncDecl<?>> toFuncDecl() {
		if (!isZ3Usable()) return Optional.empty();

		return Optional.ofNullable(func);
	}

	public Optional<Expr> makeApply(Expr thisExpr, Expr[] argExprs) {
		return makeApplyWithValueResult(thisExpr, argExprs);
	}

	public Optional<Expr> makeApplyWithTupledResult(Expr thisExpr, Expr[] argExprs) {
		return toFuncDecl().map(funcDecl -> {
			Expr[] thisAndArgsExprs =  Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisExpr);
			return model.ctx.mkApp(funcDecl, thisAndArgsExprs);
		});
	}

	public Optional<Expr> makeApplyWithStateResult(Expr thisExpr, Expr[] argExprs) {
		return toFuncDecl().map(funcDecl -> {
			Expr[] thisAndArgsExprs =  Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisExpr);
			return
					// Select the second field of the return sort
					model.ctx.mkApp(returnSort.getFieldDecls()[0],
							// Apply the method
							model.ctx.mkApp(funcDecl, thisAndArgsExprs)
					);
		});
	}

	public Optional<Expr> makeApplyWithValueResult(Expr thisExpr, Expr[] argExprs) {
		return toFuncDecl().map(funcDecl -> {
			Expr[] thisAndArgsExprs =  Z3Utils.arrayPrepend(Expr[]::new, argExprs, thisExpr);
			return
					// Select the second field of the return sort
					model.ctx.mkApp(returnSort.getFieldDecls()[1],
							// Apply the method
							model.ctx.mkApp(funcDecl, thisAndArgsExprs)
					);
		});
	}

	public Optional<Expr> makeReturnTuple(Expr state, Expr result) {
		return Optional.ofNullable(returnSort).map(sort -> model.ctx.mkApp(sort.mkDecl(), state, result));
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
		var maybePrecond = getJPrecondition();
		return maybePrecond.isPresent() && !maybePrecond.stream().anyMatch(cond -> cond instanceof TrueLiteral);
	}

	public boolean isZ3Usable() {
		return isPure() && !hasPrecondition() && func != null;
	}
}
