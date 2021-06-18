package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.Lazy;
import org.eclipse.jdt.internal.compiler.ast.Argument;

public class ArgumentModel extends VariableModel<Argument> {

	private final Lazy<Expr> constExpr;

	public ArgumentModel(Context ctx, Argument argument) {
		super(ctx, argument);
		this.constExpr = Lazy.make(() -> ctx.mkFreshConst(getName(), getSort()));
	}

	public Expr getConst() {
		return constExpr.get();
	}
}
