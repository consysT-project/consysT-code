package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

import java.util.Arrays;
import java.util.Optional;

public class MergeMethodModel extends MethodModel {


	public MergeMethodModel(Context ctx, JmlMethodDeclaration method) {
		super(ctx, method);
	}
}
