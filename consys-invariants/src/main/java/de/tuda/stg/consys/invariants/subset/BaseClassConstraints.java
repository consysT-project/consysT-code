package de.tuda.stg.consys.invariants.subset;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Tactic;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.MethodModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.parser.*;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate1;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate3;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
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
	/** The initial predicate of the class */
	private final InitialConditionModel initial;

	/** Method preconditions */
	private final Map<MethodBinding, PreconditionModel> preconditions;
	/** Method postconditions */
	private final Map<MethodBinding, PostconditionModel> postconditions;


	/* Helper classes for predicate models. */
	public static class InvariantModel extends Z3Predicate1 {
		InvariantModel(Expr thisConst, Expr body) {
			super("I", thisConst, body);
		}
	}

	public static class InitialConditionModel extends Z3Predicate1 {
		InitialConditionModel(Expr thisConst, Expr body) {
			super("init", thisConst, body);
		}
	}

	public static class PreconditionModel extends Z3Predicate1 {
		PreconditionModel(Expr thisConst, Expr body) {
			super("pre", thisConst, body);
		}
	}

	public static class PostconditionModel extends Z3Predicate3 {
		PostconditionModel(Expr oldConst, Expr thisConst, Expr resultConst, Expr body) {
			super("post", oldConst, thisConst, resultConst, body);
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

			// If the method is pure.
			if (methodModel.isZ3Usable()) {
				Expr[] args = methodModel.getArguments().stream()
						.map(argModel -> argModel.getConst().orElseThrow())
						.toArray(Expr[]::new);

				var returnSort = methodModel.getReturnType().getSort().orElseThrow();

				var s0 = classModel.toFreshConst("s0");
				var s1 = classModel.toFreshConst("s1");
				var res = model.ctx.mkFreshConst("res", returnSort);

				var application = methodModel.makeApplyWithTupledResult(s0, args).orElseThrow();
				var result = methodModel.makeReturnTuple(s1, res).orElseThrow();

				var appToState = methodModel.makeApplyWithStateResult(s0, args).orElseThrow();
				var appToValue = methodModel.makeApplyWithValueResult(s0, args).orElseThrow();

				Expr[] forallArguments = Z3Utils.arrayPrepend(Expr[]::new, args, s0, s1, res);
				var assertion =
						model.ctx.mkForall(
								forallArguments,
								model.ctx.mkImplies(
									model.ctx.mkAnd(
										preCondition.apply(s0),
										model.ctx.mkEq(
												appToState,
												s1
										),
										model.ctx.mkEq(
												appToValue,
												res
										)
									),
									postCondition.apply(s0, s1, res)
								)
								,
								1,
								null,
								null,
								null,
								null
						);




				var assertion2 =
						model.ctx.mkForall(
								forallArguments,
								postCondition.apply(
										s0,
										appToState,
										appToValue
								),
								1,
								null,
								null,
								null,
								null
						);


//				var assertion =
//						model.ctx.mkForall(
//								forallArguments,
//								postCondition.apply(
//										s0,
//										s0,
//										model.ctx.mkApp(methodModel.getZ3FuncDecl().get(), applyArguments)
//								),
//								1,
//								null,
//								null,
//								null,
//								null
//						);

				model.solver.add(assertion);
			}

		}
	}

	private InitialConditionModel handleInitialConditions(BaseClassModel classModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());

		List<Expr> initialConditions = Lists.newLinkedList();
		for (var constructor : classModel.getConstructors()) {
			var preParser = new ConstructorPreconditionExpressionParser(model, classModel, constructor);
			var preExpr = preParser.parseExpression(constructor.getJPrecondition().orElse(null));

			var postParser = new ConstructorPostconditionExpressionParser(model, classModel, constructor, thisConst);
			var postExpr = postParser.parseExpression(constructor.getJPostcondition().orElse(null));

			initialConditions.add(model.ctx.mkITE(preExpr, postExpr, model.ctx.mkFalse()));
		}

		var initialCondition = model.ctx.mkAnd(initialConditions.toArray(Expr[]::new));
		return new InitialConditionModel(thisConst, initialCondition);
	}

	private PreconditionModel handlePrecondition(MethodModel methodModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());
		var parser = new MethodPreconditionExpressionParser(model, classModel, methodModel, thisConst);
		Expr expr = parser.parseExpression(methodModel.getJPrecondition().orElse(null));
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
		Expr expr = parser.parseExpression(methodModel.getJPostcondition().orElse(null));
		// Parse the assignable clause
		BoolExpr assignable;
		var maybeClause = methodModel.getAssignableClause();
		if (maybeClause.isEmpty()) {
			Logger.warn("no assignable clause found, defaulting to assignable \\nothing: " + methodModel);
			assignable = parser.parseJmlAssignableClause(null);
		} else {
			assignable = parser.parseJmlAssignableClause(maybeClause.get());
		}
		// Combine the exprs for the postcondition
		Expr postcondition = model.ctx.mkAnd(expr, assignable);
		return new PostconditionModel(oldConst, thisConst, resultConst, postcondition);
	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public InitialConditionModel getInitialCondition() { return initial; }

	public PreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	public PostconditionModel getPostcondition(MethodBinding method) {
		return postconditions.get(method);
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
