package org.conloc.invariants.solver.subset.utils;

import com.microsoft.z3.Expr;

public interface Z3Function2 extends Z3Function {

	/**
	 * Substitutes all parameters of the predicate with the given arguments.
	 * If an argument is null, then the parameter will not be substituted.
	 * The list of arguments needs to the same size as the the list of parameters.
	 *
	 * @return An expression where the parameters have been substituted by the arguments.
	 */
	Expr apply(Expr par1, Expr par2);

}
