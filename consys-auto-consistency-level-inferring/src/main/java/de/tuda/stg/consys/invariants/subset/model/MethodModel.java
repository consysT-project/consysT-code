package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

public class MethodModel {

	private final Context ctx;
	private final JmlMethodDeclaration method;

//	private final Map<>

	public MethodModel(Context ctx, JmlMethodDeclaration method) {
		this.ctx = ctx;
		this.method = method;
	}

	public JmlMethodDeclaration getMethod() {
		return method;
	}
}
