package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.*;

import java.util.Arrays;
import java.util.Optional;

public class MethodModel {

	protected final Context ctx;
	protected final JmlMethodDeclaration method;

	protected final ArgumentModel[] args;

	public MethodModel(Context ctx, JmlMethodDeclaration method) {
		this.ctx = ctx;
		this.method = method;

		if (method.arguments == null) {
			this.args = new ArgumentModel[0];
		} else {
			this.args = Arrays.stream(method.arguments)
					.map(arg -> new ArgumentModel(ctx, arg))
					.toArray(ArgumentModel[]::new);
		}
	}

	public JmlMethodDeclaration getDecl() {
		return method;
	}

	public MethodBinding getBinding() {
		return method.binding;
	}

	public Optional<ArgumentModel> getArgument(Reference arg) {
		return Z3Utils.findReferenceInArray(args, arg, model -> model.getDecl().binding);
	}

	public Iterable<ArgumentModel> getArguments() {
		return Arrays.asList(args);
	}

	/**
	 * Returns a fresh const with sort as the return type of this method, or
	 * None if the return type is void.
	 */
	public Optional<Expr> getFreshResultConst() {
		return Z3Utils.typeBindingToSort(ctx, method.binding.returnType)
				.map(sort -> ctx.mkFreshConst("res", sort));
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

	@Override
	public String toString() {
		return String.valueOf(method.selector);
	}
}
