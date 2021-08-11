package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

public class MergeMethodModel extends MethodModel {

	public MergeMethodModel(ProgramModel smt, BaseClassModel clazz, JmlMethodDeclaration method) {
		super(smt, clazz, method);

		if (args.length != 1) {
			throw new IllegalArgumentException("merge methods needs exactly one argument, was: " + args.length);
		} else if (!"merge".equals(String.valueOf(method.selector))) {
			throw new IllegalArgumentException("merge methods has the wrong name, was: " + method.selector);
		} else if (!method.binding.returnType.equals(TypeBinding.VOID)) {
			throw new IllegalArgumentException("merge methods has wrong return type, was: " + method.binding.returnType);
		}
	}

	public Argument getArgument() {
		return method.arguments[0];
	}
}
