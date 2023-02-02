package org.conloc.invariants.solver.subset.model;

import com.google.common.collect.Lists;
import org.conloc.invariants.solver.subset.model.types.TypeModel;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

import java.util.List;

public class MergeMethodModel extends MethodModel {

	public MergeMethodModel(ProgramModel model, BaseClassModel clazz, JmlMethodDeclaration method) {
		super(model, clazz, method, false);

		if (args.length != 1) {
			throw new IllegalArgumentException("merge methods needs exactly one argument, was: " + args.length);
		} else if (!"merge".equals(String.valueOf(method.selector))) {
			throw new IllegalArgumentException("merge methods has the wrong name, was: " + method.selector);
		}

		List<TypeModel<?>> argTypes = Lists.newArrayList(model.types.typeFor(clazz.getBinding()));
		var retType = getReturnType();

		if (argTypes.stream().allMatch(TypeModel::hasSort) && retType.hasSort() /* && isPure() && !hasPrecondition() */) {
			var decls = initializeMethod(model, clazz, method, argTypes, retType);
			funcState = decls[0];
			funcValue = decls[1];
		} else {
			funcState = null;
			funcValue = null;
		}
	}

	public Argument getArgument() {
		return method.arguments[0];
	}
}
