package de.tuda.stg.consys.invariants.subset.constraints;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.*;

public class ConstraintsFactory {

	private final Z3FunctionFactory functions;
	private final String prefix;

	public ConstraintsFactory(String prefix, Z3FunctionFactory functions) {
		this.prefix = prefix;
		this.functions = functions;
	}

	public InvariantModel makeInvariantModel(Expr thisConst, Expr body) {
		return new InvariantModel(functions.makeFunction1(prefix + "$invariant", thisConst, body));
	}

	public FieldInvariantModel makeFieldInvariantModel(Expr thisConst, Expr body) {
		return new FieldInvariantModel(functions.makeFunction1(prefix + "$invariant_fields", thisConst, body));
	}

	public InitialConditionModel makeInitialConditionModel(Expr thisConst, Expr body) {
		return new InitialConditionModel(functions.makeFunction1(prefix + "$init", thisConst, body));
	}

	public MethodPreconditionModel makeMethodPreconditionModel(String methodName, Expr thisConst, Expr body) {
		return new MethodPreconditionModel(functions.makeFunction1(prefix + "$" + methodName + "$pre", thisConst, body));
	}

	public MethodPostconditionModel makeMethodPostconditionModel(String methodName, Expr oldConst, Expr thisConst, Expr returnConst, Expr body, Expr[] bodyElements) {

		var result = new Z3Function3[bodyElements.length];
		for (int i = 0; i < bodyElements.length; i++) {
			result[i] = functions.makeFunction3(prefix + "$" + methodName + "$post$" + i, oldConst, thisConst, returnConst, bodyElements[i]);
		}

		return new MethodPostconditionModel(functions.makeFunction3(prefix + "$" + methodName + "$post", oldConst, thisConst, returnConst, body), result);
	}

	public MergePreconditionModel makeMergePreconditionModel(Expr thisConst, Expr otherConst, Expr body) {
		return new MergePreconditionModel(functions.makeFunction2(prefix + "$pre_merge", thisConst, otherConst, body));
	}

	public MergePostconditionModel makeMergePostconditionModel(Expr oldConst, Expr otherConst, Expr thisConst, Expr body) {
		return new MergePostconditionModel(functions.makeFunction3(prefix + "$post_merge", oldConst, otherConst, thisConst, body));
	}

}
