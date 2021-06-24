package de.tuda.stg.consys.invariants.subset;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.model.*;
import de.tuda.stg.consys.invariants.subset.parser.*;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate1;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate2;
import de.tuda.stg.consys.invariants.subset.utils.Z3Predicate3;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlMethodSpecification;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ClassConstraints {

	private final Context ctx;
	private final ClassModel classModel;

	/** The invariant of the class */
	private final InvariantModel invariant;
	/** The initial predicate of the class */
	private final InitialConditionModel initial;

	/** Method preconditions */
	private final Map<MethodBinding, PreconditionModel> preconditions;
	/** Method postconditions */
	private final Map<MethodBinding, PostconditionModel> postconditions;

	/** Merge precondtion */
	private final MergePreconditionModel mergePrecondition;
	/** Merge postcondition */
	private final MergePostconditionModel mergePostcondition;


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

	public static class MergePreconditionModel extends Z3Predicate2 {
		MergePreconditionModel(Expr thisConst, Expr otherConst, Expr body) {
			super("pre_merge", thisConst, otherConst, body);
		}
	}

	public static class MergePostconditionModel extends Z3Predicate3 {
		MergePostconditionModel(Expr oldConst, Expr otherConst, Expr thisConst, Expr body) {
			super("post_merge", oldConst, otherConst, thisConst, body);
		}
	}




	public ClassConstraints(Context ctx, ClassModel classModel) {
		this.ctx = ctx;
		this.classModel = classModel;

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the invariant
		Expr invariantVar = ctx.mkFreshConst("s", classModel.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(ctx, classModel, invariantVar);
		Expr invariantExpr = parser.parseExpression(typ.getInvariant());
		invariant = new InvariantModel(invariantVar, invariantExpr);

		// Setup the initial condition
		initial = handleInitialConditions(classModel);

		// Setup the method pre/postconditions
		preconditions = Maps.newHashMap();
		postconditions = Maps.newHashMap();

		for(MethodModel methodModel : classModel.getMethods()) {
			handlePrecondition(methodModel);
			handlePostcondition(methodModel);
		}

		// Setup the merge pre/postcondition.
		MergeMethodModel mergeModel = classModel.getMergeMethod();
		mergePrecondition = handleMergePrecondition(mergeModel);
		mergePostcondition = handleMergePostcondition(mergeModel);

	}

	private InitialConditionModel handleInitialConditions(ClassModel classModel) {
		Expr thisConst = ctx.mkFreshConst("s", classModel.getClassSort());

		List<Expr> initialConditions = Lists.newLinkedList();
		for (var constructor : classModel.getConstructors()) {
			var preParser = new ConstructorPreconditionExpressionParser(ctx, classModel, constructor);
			var preExpr = preParser.parseExpression(constructor.getDecl().getSpecification().getPrecondition());

			var postParser = new ConstructorPostconditionExpressionParser(ctx, classModel, constructor, thisConst);
			var postExpr = postParser.parseExpression(constructor.getDecl().getSpecification().getPostcondition());

			initialConditions.add(ctx.mkITE(preExpr, postExpr, ctx.mkFalse()));
		}

		var initialCondition = ctx.mkAnd(initialConditions.toArray(Expr[]::new));
		return new InitialConditionModel(thisConst, initialCondition);
	}

	private void handlePrecondition(MethodModel methodModel) {
		var specification = methodModel.getDecl().getSpecification();

		Expr thisConst = ctx.mkFreshConst("s", classModel.getClassSort());
		var parser = new MethodPreconditionExpressionParser(ctx, classModel, methodModel, thisConst);
		Expr expr = parser.parseExpression(specification.getPrecondition());
		preconditions.put(methodModel.getDecl().binding, new PreconditionModel(thisConst, expr));
	}

	private MergePreconditionModel handleMergePrecondition(MergeMethodModel methodModel) {
		JmlMethodSpecification specification = methodModel.getDecl().getSpecification();

		Expr thisConst = ctx.mkFreshConst("s", classModel.getClassSort());
		Expr otherConst = ctx.mkFreshConst("s_other", classModel.getClassSort());
		var parser = new MergeMethodPreconditionExpressionParser(ctx, classModel, methodModel, thisConst, otherConst);
		Expr expr = parser.parseExpression(specification.getPrecondition());
		return new MergePreconditionModel(thisConst, otherConst, expr);
	}

	private MergePostconditionModel handleMergePostcondition(MergeMethodModel methodModel) {
		JmlMethodSpecification specification = methodModel.getDecl().getSpecification();

		Expr oldConst = ctx.mkFreshConst("s_old", classModel.getClassSort());
		Expr thisConst = ctx.mkFreshConst("s_new", classModel.getClassSort());
		Expr otherConst = ctx.mkFreshConst("s_other", classModel.getClassSort());

		var parser = new MergeMethodPostconditionExpressionParser(ctx, classModel, methodModel, thisConst, oldConst, otherConst);
		Expr expr = parser.parseExpression(specification.getPostcondition());
		return new MergePostconditionModel(oldConst, otherConst, thisConst, expr);
	}


	private void handlePostcondition(MethodModel methodModel) {
		JmlMethodSpecification specification = methodModel.getDecl().getSpecification();

		// Var for `\old(this)` references
		Expr oldConst = ctx.mkFreshConst("s_old", classModel.getClassSort());
		// Var for `this` references
		Expr thisConst = ctx.mkFreshConst("s_new", classModel.getClassSort());
		// Var for \result references
		Expr resultConst = methodModel.getFreshResultConst();

		// Parse the postcondition from JML @ensures specification
		var parser = new MethodPostconditionExpressionParser(ctx, classModel, methodModel, thisConst, oldConst, resultConst);
		Expr expr = parser.parseExpression(specification.getPostcondition());
		// Parse the assignable clause
		BoolExpr assignable;
		var maybeClause = methodModel.getAssignableClause();
		if (maybeClause.isEmpty()) {
			throw new IllegalArgumentException("no assignable clause for " + methodModel.getDecl());
		} else {
			assignable = parser.parseJmlAssignableClause(maybeClause.get());
		}
		// Combine the exprs for the postcondition
		Expr postcondition = ctx.mkAnd(expr, assignable);
		postconditions.put(methodModel.getDecl().binding, new PostconditionModel(oldConst, thisConst, resultConst, postcondition));
	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public InitialConditionModel getInitialCondition() { return initial; }

	public MergePreconditionModel getMergePrecondition() {
		return mergePrecondition;
	}

	public MergePostconditionModel getMergePostcondition() {
		return mergePostcondition;
	}

	public PreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	public PostconditionModel getPostcondition(MethodBinding method) {
		return postconditions.get(method);
	}

	public ClassModel getClassModel() {
		return classModel;
	}

	@Override
	public String toString() {
		return "Class" + classModel.getClassName() + "====\n"
				+ "Invariant ====\n" + getInvariant() + "\n"
				+ "Initial ====\n" + getInitialCondition() + "\n"
				+ "Preconditions ====\n" + preconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining())
				+ "Postconditions ====\n" + postconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining())
				+ "Merge Precondition ====\n" +  getMergePrecondition()  + "\n"
				+ "Merge Postcondition ====\n" +  getMergePostcondition();
	}
}
