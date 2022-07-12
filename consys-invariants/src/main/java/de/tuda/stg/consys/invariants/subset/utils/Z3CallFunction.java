package de.tuda.stg.consys.invariants.subset.utils;

import com.google.common.collect.Lists;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import java.util.Arrays;
import java.util.List;

public class Z3CallFunction extends AbstractZ3Function {
	protected final FuncDecl func;

	public Z3CallFunction(String name, FuncDecl func) {
		super(name);
		this.func = func;
	}

	/**
	 * Substitutes all parameters of the predicate with the given arguments.
	 * If an argument is null, then the parameter will not be substituted.
	 * The list of arguments needs to the same size as the the list of parameters.
	 *
	 * @return An expression where the parameters have been substituted by the arguments.
	 */
	@Override
	public Expr apply(Expr... args) {
		if (args.length != func.getArity())
			throw new IllegalArgumentException("args.length != parameters.length");

		return func.apply(args);
	}

	@Override
	public String toString() {
		return "<FUNC>" + func.toString();
	}

}
