package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import org.eclipse.jdt.internal.compiler.ast.AbstractVariableDeclaration;

public class VariableModel<VarDecl extends AbstractVariableDeclaration> {

	protected final ProgramModel model;
	protected final VarDecl varDecl;

	private final String name;
	private final TypeModel<?> type;


	public VariableModel(ProgramModel model, VarDecl varDecl) {
		this.model = model;
		this.varDecl = varDecl;
		this.name = String.valueOf(varDecl.name);
		this.type = model.types.typeFor(varDecl.type);
	}

	public String getName() {
		return name;
	}

	public TypeModel<?> getType() {
		return type;
	}

	@Override
	public String toString() {
		return "VarModel[" + varDecl + "]";
	}

//	public VarDecl getDecl() {
//		return varDecl;
//	}


}
