package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Maps;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.parser.ClassExpressionParser;
import de.tuda.stg.consys.invariants.subset.parser.MethodPostconditionExpressionParser;
import de.tuda.stg.consys.invariants.subset.parser.MethodPreconditionExpressionParser;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class ParsedClassModel {

	private final Context ctx;
	private final ClassModel classModel;

	private final InvariantModel invariant;

	private final Map<MethodBinding, PreconditionModel> preconditions;
	private final Map<MethodBinding, PostconditionModel> postconditions;

	public ParsedClassModel(Context ctx, ClassModel classModel) {
		this.ctx = ctx;
		this.classModel = classModel;

		JmlTypeDeclaration typ = classModel.getJmlType();

		// Setup the invariant
		Expr invariantVar = ctx.mkFreshConst("s0", classModel.getClassSort());
		ClassExpressionParser parser = new ClassExpressionParser(ctx, classModel, invariantVar);
		Expr invariantExpr = parser.parseExpression(typ.getInvariant());
		invariant = new InvariantModel(invariantVar, invariantExpr);

		// Setup the pre/postconditions
		preconditions = Maps.newHashMap();
		postconditions = Maps.newHashMap();

		for(MethodModel methodModel : classModel.getMethods()) {

			Expr preconditionVar = ctx.mkFreshConst("s0", classModel.getClassSort());

			MethodPreconditionExpressionParser methodPreParser = new MethodPreconditionExpressionParser(ctx, classModel, methodModel, preconditionVar);
			Expr preconditionExpr = methodPreParser.parseExpression(methodModel.getMethod().getSpecification().getPrecondition());
			preconditions.put(methodModel.getMethod().binding, new PreconditionModel(preconditionVar, preconditionExpr));


			// Var for `this` references
			Expr postThisConst = ctx.mkFreshConst("s0", classModel.getClassSort());
			// Var for `\old(this)` references
			Expr postOldConst = ctx.mkFreshConst("s1", classModel.getClassSort());
			Optional<Expr> postResultConst = methodModel.getFreshResultConst();

			MethodPostconditionExpressionParser methodPostParser = new MethodPostconditionExpressionParser(ctx, classModel, methodModel, postThisConst, postOldConst, postResultConst);
			Expr postConditionExpr = methodPostParser.parseExpression(methodModel.getMethod().getSpecification().getPostcondition());
			postconditions.put(methodModel.getMethod().binding, new PostconditionModel(postOldConst, postThisConst, postConditionExpr, postResultConst));

		}

	}

	public InvariantModel getInvariant() {
		return invariant;
	}

	public PreconditionModel getPrecondition(MethodBinding method) {
		return preconditions.get(method);
	}

	@Override
	public String toString() {
		return "Class" + classModel.getClassName() + "====\n"
				+ "Invariant ====\n" + getInvariant() + "\n"
				+ "Preconditions ====\n" + preconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining())
				+ "Postconditions ====\n" + postconditions.entrySet().stream().map(entry -> String.valueOf(entry.getKey().selector) + ": " + entry.getValue() + "\n").collect(Collectors.joining());
	}
}
