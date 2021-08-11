package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;

public class ConstructorModel extends AbstractMethodModel<JmlConstructorDeclaration> {

	public ConstructorModel(ProgramModel smt, BaseClassModel clazz, JmlConstructorDeclaration method) {
		super(smt, clazz, method);
	}
}
