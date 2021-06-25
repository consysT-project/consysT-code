package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.FuncDecl;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	// A function declaration to be used in z3. Is null if the method types do not conform to z3 types.
	private final FuncDecl<?> func;

	public MethodModel(Z3Binding smt, ClassModel clazz, JmlMethodDeclaration method) {
		super(smt, clazz, method);

		var argSorts = getArgumentSorts();
		var retSort = getReturnSort();

		if (argSorts.isPresent() && retSort.isPresent()) {
			func = smt.ctx.mkFreshFuncDecl(getName(), argSorts.get(), retSort.get());
		} else {
			func = null;
		}
	}

	public Optional<FuncDecl<?>> getZ3FuncDecl() {
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
				throw new IllegalStateException("jml spec case not supported: " + rest);
			}
		}

		return Optional.ofNullable(result);
	}
}
