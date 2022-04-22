package de.tuda.stg.consys.invariants.subset.utils;

import com.google.common.collect.Lists;
import com.microsoft.z3.Expr;

import java.util.Arrays;
import java.util.List;

public class Z3Function {
	protected final String name;

	protected final Expr[] parameters;
	protected final Expr body;


	public Z3Function(String name, Expr[] parameters, Expr body) {
		this.name = name;
		this.parameters = parameters;
		this.body = body.simplify();
	}

	/**
	 * Substitutes all parameters of the predicate with the given arguments.
	 * If an argument is null, then the parameter will not be substituted.
	 * The list of arguments needs to the same size as the the list of parameters.
	 *
	 * @return An expression where the parameters have been substituted by the arguments.
	 */
	protected Expr apply(Expr... args) {
		if (args.length != parameters.length)
			throw new IllegalArgumentException("args.length != parameters.length");

		List<Expr> _params = Lists.newLinkedList();
		List<Expr> _args = Lists.newLinkedList();
		for (int i = 0; i < args.length; i++) {
			if (args[i] != null) {
				_params.add(parameters[i]);
				_args.add(args[i]);
			}
		}

		var result = body.substitute(_params.toArray(Expr[]::new), _args.toArray(Expr[]::new));
		return result;
	}

	@Override
	public String toString() {
		return name + Arrays.toString(parameters) + " = " + body;
	}

}
