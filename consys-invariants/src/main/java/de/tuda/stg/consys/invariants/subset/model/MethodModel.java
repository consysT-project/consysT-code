package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import org.jmlspecs.jml4.ast.*;

import java.util.Optional;

public class MethodModel extends AbstractMethodModel<JmlMethodDeclaration>{

	public MethodModel(Context ctx, JmlMethodDeclaration method) {
		super(ctx, method);
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
