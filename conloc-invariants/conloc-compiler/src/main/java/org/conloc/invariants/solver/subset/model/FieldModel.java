package org.conloc.invariants.solver.subset.model;

import com.microsoft.z3.FuncDecl;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class FieldModel extends VariableModel<FieldDeclaration>{

	private FuncDecl<?> accessor;

	public FieldModel(ProgramModel smt, FieldDeclaration fieldDeclaration, FuncDecl<?> accessor) {
		super(smt, fieldDeclaration);
		this.accessor = accessor;
	}

	void initAccessor(FuncDecl<?> accessor) {
		if (this.accessor != null)
			throw new IllegalStateException("accessor was already initialized.");

		this.accessor = accessor;
	}

	public FuncDecl getAccessor() {
		return accessor;
	}

	public FieldBinding getBinding() {
		return varDecl.binding;
	}

	public TypeBinding getTypeBinding() {
		return varDecl.binding.type;
	}
}
