package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

import java.util.Arrays;
import java.util.Optional;

public abstract class AbstractMethodModel<Decl extends AbstractMethodDeclaration> {

	protected final Context ctx;
	protected final Decl method;

	protected final ArgumentModel[] args;

	public AbstractMethodModel(Context ctx, Decl method) {
		this.ctx = ctx;
		this.method = method;

		if (method.arguments == null) {
			this.args = new ArgumentModel[0];
		} else {
			this.args = Arrays.stream(method.arguments)
					.map(arg -> new ArgumentModel(ctx, arg))
					.toArray(ArgumentModel[]::new);
		}
	}

	public Decl getDecl() {
		return method;
	}

	public MethodBinding getBinding() {
		return method.binding;
	}

	public Optional<ArgumentModel> getArgument(Reference arg) {
		return Z3Utils.findReferenceInArray(args, arg, model -> model.getDecl().binding);
	}

	public boolean returnsVoid() {
		return TypeBinding.VOID.equals(method.binding.returnType);
	}

	public Iterable<ArgumentModel> getArguments() {
		return Arrays.asList(args);
	}

	/**
	 * Returns a fresh const with sort as the return type of this method, or
	 * None if the return type is void.
	 */
	public Expr getFreshResultConst() {
		return Z3Utils.typeBindingToSort(ctx, method.binding.returnType)
				.map(sort -> ctx.mkFreshConst("res", sort))
				.orElseGet(() -> ctx.mkFreshConst("res", ctx.getIntSort()));
	}

	@Override
	public String toString() {
		return String.valueOf(method.selector);
	}
}
