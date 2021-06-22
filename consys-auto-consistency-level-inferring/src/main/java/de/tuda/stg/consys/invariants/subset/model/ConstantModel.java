package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;

public class ConstantModel extends VariableModel<FieldDeclaration> {

	private final Expr value;

	public ConstantModel(Context ctx, FieldDeclaration fieldDeclaration, Expr value) {
		super(ctx, fieldDeclaration);
		this.value = value.simplify();
	}

	public Expr getValue() {
		return value;
	}
}
