package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.eclipse.jdt.internal.compiler.ast.Argument;

import java.util.Optional;

public class ArgumentModel extends VariableModel<Argument> {

	private final Expr constExpr;

	public ArgumentModel(Z3Binding smt, Argument argument) {
		super(smt, argument);
		this.constExpr = getSort().map(sort -> smt.ctx.mkFreshConst(getName(), sort)).orElse(null);
	}

	public Optional<Expr> getConst() {
		return Optional.of(constExpr);
	}

}
