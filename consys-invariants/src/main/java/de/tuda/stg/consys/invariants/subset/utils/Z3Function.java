package de.tuda.stg.consys.invariants.subset.utils;

import com.google.common.collect.Lists;
import com.microsoft.z3.Expr;

import java.util.Arrays;
import java.util.List;

public interface Z3Function {

	/**
	 * Substitutes all parameters of the predicate with the given arguments.
	 * If an argument is null, then the parameter will not be substituted.
	 * The list of arguments needs to the same size as the the list of parameters.
	 *
	 * @return An expression where the parameters have been substituted by the arguments.
	 */
	Expr apply(Expr... args);

//	Expr getParameter(int index);

}
