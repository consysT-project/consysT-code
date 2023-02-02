package de.tuda.stg.consys.invariants.solver.subset.constraints;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.solver.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.solver.subset.model.MethodModel;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.model.types.ObjectModel;
import de.tuda.stg.consys.invariants.solver.subset.parser.*;
import de.tuda.stg.consys.invariants.solver.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.solver.subset.utils.Z3SubstitutionFunctionFactory;
import de.tuda.stg.consys.invariants.solver.subset.utils.Z3Utils;
import de.tuda.stg.consys.logging.Logger;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class BaseClassConstraints<CModel extends BaseClassModel> {

	public final ProgramModel model;
	public final CModel classModel;

	protected final ConstraintsFactory constraintsFactory;

	/** The invariant of the class */
	private final InvariantModel invariant;
	/** The invariants of all fields of the class */
	private final FieldInvariantModel fieldInvariant;
	/** The initial predicate of the class */
	private final InitialConditionModel initial;

	/** Method preconditions */
	private final Map<MethodBinding, MethodPreconditionModel> preconditions;
	/** Method postconditions */
	private final Map<MethodBinding, MethodPostconditionModel> postconditions;


	public BaseClassConstraints(ProgramModel model, CModel classModel) {
		this.model = model;
		this.classModel = classModel;

		this.constraintsFactory = new ConstraintsFactory(classModel.getClassName(), new Z3SubstitutionFunctionFactory());

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the invariant
		Expr invariantVar = model.ctx.mkFreshConst("s", classModel.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(model, classModel, invariantVar);
		Expr invariantExpr = parser.parseExpression(typ.getInvariant());



		invariant = constraintsFactory.makeInvariantModel(invariantVar, invariantExpr);

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
		fieldInvariant = constraintsFactory.makeFieldInvariantModel(fieldInvariantVar, fieldInvariantExpr);


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
//				var s1 = classModel.toFreshConst("s1");

				var appToState = methodModel.makeApplyReturnState(s0, args).orElseThrow();
				var appToValue = methodModel.makeApplyReturnValue(s0, args).orElseThrow();

				Expr[] forallArguments = Z3Utils.arrayPrepend(Expr[]::new, args, s0);

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
		return constraintsFactory.makeInitialConditionModel(thisConst, initialCondition);
	}

	private MethodPreconditionModel handlePrecondition(MethodModel methodModel) {
		Expr thisConst = model.ctx.mkFreshConst("s", classModel.getClassSort());
		var parser = new MethodPreconditionExpressionParser(model, classModel, methodModel, thisConst);
		Expr expr = parser.parseExpression(methodModel.getJmlPrecondition().orElse(null));
		return constraintsFactory.makeMethodPreconditionModel(methodModel.getName(),thisConst, expr);
	}



	private MethodPostconditionModel handlePostcondition(MethodModel methodModel) {
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
			assignable = parser.parseJmlAssignableClause(null);
		} else {
			assignable = parser.parseJmlAssignableClause(maybeClause.get());
		}
		// Combine the exprs for the postcondition
		exprs[0] = assignable;
		return constraintsFactory.makeMethodPostconditionModel(methodModel.getName(), oldConst, thisConst, resultConst, model.ctx.mkAnd(exprs), exprs);
	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public FieldInvariantModel getFieldInvariant() {
		return fieldInvariant;
	}

	public InitialConditionModel getInitialCondition() { return initial; }

	public MethodPreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	public MethodPostconditionModel getPostcondition(MethodBinding method) {
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
