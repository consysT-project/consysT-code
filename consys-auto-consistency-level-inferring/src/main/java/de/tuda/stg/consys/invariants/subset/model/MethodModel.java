package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

import java.util.Arrays;
import java.util.Optional;

public class MethodModel {

	private final Context ctx;
	private final JmlMethodDeclaration method;

	private final ArgumentModel[] args;

	public MethodModel(Context ctx, JmlMethodDeclaration method) {
		this.ctx = ctx;
		this.method = method;

		if (method.arguments == null) {
			this.args = new ArgumentModel[0];
		} else {
			this.args = Arrays.stream(method.arguments)
					.map(arg -> new ArgumentModel(ctx, arg))
					.toArray(ArgumentModel[]::new);
		}
		System.out.println("hello");
	}

	public JmlMethodDeclaration getMethod() {
		return method;
	}

	public Optional<ArgumentModel> getArgument(Reference arg) {
		return Z3Utils.findReferenceInArray(args, arg, model -> model.getDecl().binding);
	}
}
