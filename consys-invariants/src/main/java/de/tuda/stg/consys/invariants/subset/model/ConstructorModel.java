package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

public class ConstructorModel extends AbstractMethodModel<JmlConstructorDeclaration> {

	public ConstructorModel(Context ctx, JmlConstructorDeclaration method) {
		super(ctx, method);
	}
}
