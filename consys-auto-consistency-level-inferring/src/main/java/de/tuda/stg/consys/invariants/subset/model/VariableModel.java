package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.Lazy;
import org.eclipse.jdt.internal.compiler.ast.AbstractVariableDeclaration;

public class VariableModel<VarDecl extends AbstractVariableDeclaration> {

	protected final Context ctx;
	protected final VarDecl varDecl;

	private final Lazy<String> name;
	private final Lazy<Sort> sort;


	public VariableModel(Context ctx, VarDecl varDecl) {
		this.ctx = ctx;
		this.varDecl = varDecl;
		this.name = Lazy.make(() -> String.valueOf(varDecl.name));
		this.sort = Lazy.make(() -> Z3Utils.typeReferenceToSort(ctx, varDecl.type).orElseThrow());
	}


	public String getName() {
		return name.get();
	}

	public Sort getSort() {
		return sort.get();
	}

	public VarDecl getDecl() {
		return varDecl;
	}
}
