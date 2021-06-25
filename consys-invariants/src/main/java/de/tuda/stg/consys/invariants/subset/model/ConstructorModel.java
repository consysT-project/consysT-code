package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.utils.Z3Binding;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;

public class ConstructorModel extends AbstractMethodModel<JmlConstructorDeclaration> {

	public ConstructorModel(Z3Binding smt, ClassModel clazz, JmlConstructorDeclaration method) {
		super(smt, clazz, method);
	}
}
