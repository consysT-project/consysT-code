package org.conloc.invariants.solver.subset.model;

import com.microsoft.z3.Expr;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;

public class ConstantModel extends VariableModel<FieldDeclaration> {

	private final Expr value;

	public ConstantModel(ProgramModel smt, FieldDeclaration fieldDeclaration, Expr value) {
		super(smt, fieldDeclaration);
		this.value = value.simplify();
	}

	public Expr getValue() {
		return value;
	}

	public FieldBinding getBinding() {
		return varDecl.binding;
	}
}
