package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	private final FuncDecl<?> func;

	public MethodModel(ProgramModel smt, BaseClassModel clazz, JmlMethodDeclaration method) {
		super(smt, clazz, method);

		var argTypes = getArgumentTypes();
		var retType = getReturnType();

		if (argTypes.stream().allMatch(TypeModel::hasSort) && retType.hasSort() && isPure() && !hasPrecondition()) {
			// Add `this` and `\old this` to the arguments of the z3 function.
			var argSorts = argTypes.stream().map(TypeModel::toSort).toArray(Sort[]::new);
			var argSortsAndThis = Z3Utils.arrayPrepend(Sort[]::new, argSorts, clazz.getClassSort(), clazz.getClassSort());

			func = smt.ctx.mkFreshFuncDecl(getName(), argSortsAndThis, retType.toSort());
		} else {
			func = null;
		}
	}

	public Optional<FuncDecl<?>> getZ3FuncDecl() {
		if (!isZ3Usable()) return Optional.empty();

		return Optional.ofNullable(func);
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
