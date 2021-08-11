package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.FuncDecl;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;

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

	@Override
	public String toString() {
		return "FieldModel[" + getDecl() + "]";
	}

	public boolean isArray() {
		return varDecl.binding.type.isArrayType();
	}
}
