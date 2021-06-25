package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;

public class ConstantModel extends VariableModel<FieldDeclaration> {

	private final Expr value;

	public ConstantModel(Z3Binding smt, FieldDeclaration fieldDeclaration, Expr value) {
		super(smt, fieldDeclaration);
		this.value = value.simplify();
	}

	public Expr getValue() {
		return value;
	}
}
