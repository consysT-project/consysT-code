package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Lists;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.exceptions.UnsupportedJMLExpression;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.jmlspecs.jml4.ast.*;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	private final FuncDecl<?> func;

	public MethodModel(Z3Binding smt, ClassModel clazz, JmlMethodDeclaration method) {
		super(smt, clazz, method);

		var argSorts = getArgumentSorts();
		var retSort = getReturnSort();

		if (argSorts.isPresent() && retSort.isPresent() && isPure() && !hasPrecondition()) {
			// Add `this` and `\old this` to the arguments of the z3 function.
			Sort[] argSortsAndThis = Z3Utils.arrayPrepend(Sort[]::new, argSorts.get(), clazz.getClassSort(), clazz.getClassSort());
			func = smt.ctx.mkFreshFuncDecl(getName(), argSortsAndThis, retSort.get());
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

		for (JmlSpecCase jmlSpecCase : getDecl().getSpecification().getSpecCases()) {
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
				System.err.println("jml spec case not supported: " + rest);
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
		return !(getDecl().getSpecification().getPrecondition() instanceof TrueLiteral);
	}

	public boolean isZ3Usable() {
		return isPure() && !hasPrecondition() && func != null;
	}
}
