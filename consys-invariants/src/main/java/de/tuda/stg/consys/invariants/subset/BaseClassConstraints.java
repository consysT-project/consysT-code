package de.tuda.stg.consys.invariants.subset;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.model.types.ObjectModel;
import de.tuda.stg.consys.invariants.subset.parser.*;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.subset.utils.Z3Function1;
import de.tuda.stg.consys.invariants.subset.utils.Z3Function3;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class BaseClassConstraints<CModel extends BaseClassModel> {

	final ProgramModel model;
	final CModel classModel;

	/** The invariant of the class */
	private final InvariantModel invariant;
	/** The invariants of all fields of the class */
	private final FieldInvariantModel fieldInvariant;
	/** The initial predicate of the class */
	private final InitialConditionModel initial;

	/** Method preconditions */
	private final Map<MethodBinding, PreconditionModel> preconditions;
	/** Method postconditions */
	private final Map<MethodBinding, PostconditionModel> postconditions;


	/* Helper classes for predicate models. */
	/** Handles the user-defined invariant */
	public static class InvariantModel extends Z3Function1 {
		InvariantModel(Expr thisConst, Expr body) {
			super("I", thisConst, body);
		}
	}

	public static class FieldInvariantModel extends Z3Function1 {
		FieldInvariantModel(Expr thisConst, Expr body) {
			super("I_fields", thisConst, body);
		}
	}

	public static class InitialConditionModel extends Z3Function1 {
		InitialConditionModel(Expr thisConst, Expr body) {
			super("init", thisConst, body);
		}
	}

	public static class PreconditionModel extends Z3Function1 {
		PreconditionModel(Expr thisConst, Expr body) {
			super("pre", thisConst, body);
		}
	}

	public static class PostconditionModel extends Z3Function3 {
		private final Expr[] bodyElements;

		PostconditionModel(Expr oldConst, Expr thisConst, Expr resultConst, Expr body, Expr[] bodyElements) {
			super("post", oldConst, thisConst, resultConst, body);
			this.bodyElements = bodyElements;
		}

		@Override
		public Expr apply(Expr arg1, Expr arg2, Expr arg3) {
//			throw new UnsupportedOperationException();
			return super.apply(arg1, arg2, arg3);
		}

		public Expr[] applyWithSplitBody(Expr oldArg, Expr thisArg, Expr resultArg) {
			var result = new Expr[bodyElements.length];
			for (int i = 0; i < bodyElements.length; i++) {
				Z3Function3 pred = new Z3Function3("post_" + i, parameters[0], parameters[1], parameters[2], bodyElements[i]);
				result[i] = pred.apply(oldArg, thisArg, resultArg);
			}

			return result;
		}
	}


	public BaseClassConstraints(ProgramModel model, CModel classModel) {
		this.model = model;
		this.classModel = classModel;

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the invariant
		Expr invariantVar = model.ctx.mkFreshConst("s", classModel.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(model, classModel, invariantVar);
		Expr invariantExpr = parser.parseExpression(typ.getInvariant());

		invariant = new InvariantModel(invariantVar, invariantExpr);

		// Setup the field invariants
		Expr fieldInvariantVar = model.ctx.mkFreshConst("s", classModel.getClassSort());
		Expr fieldInvariantExpr = model.ctx.mkTrue();
		for (var fieldModel : classModel.getFields()) {
			if (fieldModel.getType() instanceof ObjectModel) {
				var refBinding = ((ObjectModel) fieldModel.getType()).getRefBinding();
				var mbFieldConstraints = model.getClassConstraints(refBinding);
				if (mbFieldConstraints.isEmpty()) {
					Logger.warn("cannot get constraints for class " + JDTUtils.nameOfClass(refBinding));
					continue;
				}
				var fieldConstraints = mbFieldConstraints.get();
				fieldInvariantExpr = model.ctx.mkAnd(fieldInvariantExpr,
						// Add the invariant of the field
						fieldConstraints.getInvariant().apply(fieldModel.getAccessor().apply(fieldInvariantVar)),
						// and all the field invariants
						fieldConstraints.getFieldInvariant().apply(fieldModel.getAccessor().apply(fieldInvariantVar))
				).simplify();

			}
		}
		fieldInvariant = new FieldInvariantModel(fieldInvariantVar, fieldInvariantExpr);


		// Setup the initial condition
		initial = handleInitialConditions(classModel);

		// Setup the method pre/postconditions
		preconditions = Maps.newHashMap();
		postconditions = Maps.newHashMap();
		for(MethodModel methodModel : classModel.getMethods()) {
			var preCondition = handlePrecondition(methodModel);
			preconditions.put(methodModel.getBinding(), preCondition);
			var postCondition = handlePostcondition(methodModel);
			postconditions.put(methodModel.getBinding(), postCondition);

			// Add the constraint that defines the method if it is usable as constraint
			if (methodModel.usableAsConstraint()) {
				Expr[] args = methodModel.getArguments().stream()
						.map(argModel -> argModel.getConst().orElseThrow())
						.toArray(Expr[]::new);

				var s0 = classModel.toFreshConst("s0");
				var s1 = classModel.toFreshConst("s1");

				var appToState = methodModel.makeApplyReturnState(s0, args).orElseThrow();
				var appToValue = methodModel.makeApplyReturnValue(s0, args).orElseThrow();

				Expr[] forallArguments = Z3Utils.arrayPrepend(Expr[]::new, args, s0, s1);

				var conds =  postCondition.applyWithSplitBody(
						s0,
						appToState,
						appToValue
				);

				for (var cond : conds) {
					var assertion =
							model.ctx.mkForall(
									forallArguments,
									cond,
									1,
									null,
									null,
									null,
									null
							);
					model.solver.add(assertion);
				}

			}
		}
	}

	private InitialConditionModel handleInitialConditions(BaseClassModel classModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());

		List<Expr> initialConditions = Lists.newLinkedList();
		for (var constructor : classModel.getConstructors()) {
			var preParser = new ConstructorPreconditionExpressionParser(model, classModel, constructor);
			var preExpr = preParser.parseExpression(constructor.getJmlPrecondition().orElse(null));

			var postParser = new ConstructorPostconditionExpressionParser(model, classModel, constructor, thisConst);
			var postExpr = postParser.parseExpression(constructor.getJmlPostcondition().orElse(null));

			initialConditions.add(model.ctx.mkITE(preExpr, postExpr, model.ctx.mkFalse()));
		}

		var initialCondition = model.ctx.mkAnd(initialConditions.toArray(Expr[]::new));
		return new InitialConditionModel(thisConst, initialCondition);
	}

	private PreconditionModel handlePrecondition(MethodModel methodModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());
		var parser = new MethodPreconditionExpressionParser(model, classModel, methodModel, thisConst);
		Expr expr = parser.parseExpression(methodModel.getJmlPrecondition().orElse(null));
		return new PreconditionModel(thisConst, expr);
	}



	private PostconditionModel handlePostcondition(MethodModel methodModel) {
		// Var for `\old(this)` references
		Expr oldConst = model.ctx.mkFreshConst("s_old", classModel.getClassSort());
		// Var for `this` references
		Expr thisConst = model.ctx.mkFreshConst("s_new", classModel.getClassSort());
		// Var for \result references
		Expr resultConst = methodModel.getReturnType().getSort()
			.map(sort -> model.ctx.mkFreshConst("res", sort))
			.orElse(null);

		// Parse the postcondition from JML @ensures specification
		var parser = new MethodPostconditionExpressionParser(model, classModel, methodModel, thisConst, oldConst, resultConst);

		var jmlConds = splitAndExpression(methodModel.getJmlPostcondition().orElse(null));

		Expr[] exprs = new Expr[jmlConds.length + 1];
		for (int i = 0; i < jmlConds.length; i++) {
			var e = parser.parseExpression(jmlConds[i]);
			exprs[i + 1] = e;
		}


		// Parse the assignable clause
		BoolExpr assignable;
		var maybeClause = methodModel.getAssignableClause();
		if (maybeClause.isEmpty()) {
			Logger.warn("no assignable clause found, defaulting to assignable \\nothing. Method: " + methodModel);
			assignable = parser.parseJmlAssignableClause(null);
		} else {
			assignable = parser.parseJmlAssignableClause(maybeClause.get());
		}
		// Combine the exprs for the postcondition
		exprs[0] = assignable;
		return new PostconditionModel(oldConst, thisConst, resultConst, model.ctx.mkAnd(exprs), exprs);
	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public FieldInvariantModel getFieldInvariant() {
		return fieldInvariant;
	}

	public InitialConditionModel getInitialCondition() { return initial; }

	public PreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	public PostconditionModel getPostcondition(MethodBinding method) {
		return postconditions.get(method);
	}

	private Expression[] splitAndExpression(Expression expr) {

		if (expr instanceof BinaryExpression) {
			BinaryExpression binExpr = (BinaryExpression) expr;
			String operator = binExpr.operatorToString();

			if ("&".equals(operator) || "&&".equals(operator)) {
				var lhs = splitAndExpression(binExpr.left);
				var rhs = splitAndExpression(binExpr.right);

				var result = new Expression[lhs.length + rhs.length];
				System.arraycopy(lhs, 0, result, 0, lhs.length);
				System.arraycopy(rhs, 0, result, lhs.length, rhs.length);

				return result;
			}

		}

		return new Expression[]{expr};

	}


	public BaseClassModel getClassModel() {
		return classModel;
	}

//	private Expr getForallInvariant(InvariantModel inv) {
//		var forallVar = model.ctx.mkFreshConst("s_inv", classModel.getClassSort());
//		model.ctx.mkForall(
//				new Expr[] {forallVar},
//				model.ctx.mkTrue(),
//
//
//		)
//	}

	@Override
	public String toString() {
		return "Class" + classModel.getClassName() + "====\n"
				+ "Invariant ====\n" + getInvariant() + "\n"
				+ "Initial ====\n" + getInitialCondition() + "\n"
				+ "Preconditions ====\n" + preconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining())
				+ "Postconditions ====\n" + postconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining());
	}



}
