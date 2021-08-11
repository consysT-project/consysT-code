package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.Argument;

import java.util.Optional;

public class ArgumentModel extends VariableModel<Argument> {

	private final Expr constExpr;

	public ArgumentModel(ProgramModel smt, Argument argument) {
		super(smt, argument);
		this.constExpr = getType().getSort().map(sort -> smt.ctx.mkFreshConst(getName(), sort)).orElse(null);
	}

	public Optional<Expr> getConst() {
		return Optional.of(constExpr);
	}

}
