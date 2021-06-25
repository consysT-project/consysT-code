package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractVariableDeclaration;

import java.util.Optional;

public class VariableModel<VarDecl extends AbstractVariableDeclaration> {

	protected final Z3Binding smt;
	protected final VarDecl varDecl;

	private final String name;
	private final Sort sort;


	public VariableModel(Z3Binding smt, VarDecl varDecl) {
		this.smt = smt;
		this.varDecl = varDecl;
		this.name = String.valueOf(varDecl.name);
		this.sort = Z3Utils.typeReferenceToSort(smt.ctx, varDecl.type).orElse(null);
	}


	public String getName() {
		return name;
	}

	/** Returns the sort of this variable or empty if there is no matching Z3 sort. */
	public Optional<Sort> getSort() {
		return Optional.ofNullable(sort);
	}

	public VarDecl getDecl() {
		return varDecl;
	}


}
