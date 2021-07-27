package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractVariableDeclaration;

import java.util.Optional;

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

	public VarDecl getDecl() {
		return varDecl;
	}


}
