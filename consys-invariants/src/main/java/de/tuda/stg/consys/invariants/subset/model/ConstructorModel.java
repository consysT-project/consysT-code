package de.tuda.stg.consys.invariants.subset.model;

import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;

public class ConstructorModel extends AbstractMethodModel<JmlConstructorDeclaration> {

	public ConstructorModel(ProgramModel smt, ClassModel clazz, JmlConstructorDeclaration method) {
		super(smt, clazz, method);
	}
}
