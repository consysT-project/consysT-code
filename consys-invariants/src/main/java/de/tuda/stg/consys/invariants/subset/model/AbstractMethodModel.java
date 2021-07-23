package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

public abstract class AbstractMethodModel<Decl extends AbstractMethodDeclaration> {

	protected final ProgramModel smt;
	protected final ClassModel clazz;
	protected final Decl method;

	protected final ArgumentModel[] args;

	public AbstractMethodModel(ProgramModel smt, ClassModel clazz, Decl method) {
		this.smt = smt;
		this.clazz = clazz;
		this.method = method;

		if (method.arguments == null) {
			this.args = new ArgumentModel[0];
		} else {
			this.args = Arrays.stream(method.arguments)
					.map(arg -> new ArgumentModel(smt, arg))
					.toArray(ArgumentModel[]::new);
		}
	}

	public Decl getDecl() {
		return method;
	}

	public String getName() {
		return String.valueOf(method.selector);
	}

	public MethodBinding getBinding() {
		return method.binding;
	}

	public Optional<ArgumentModel> getArgument(Reference arg) {
		return Z3Utils.findReferenceInArray(args, arg, model -> model.getDecl().binding);
	}

	public boolean returnsVoid() {
		return TypeBinding.VOID.equals(method.binding.returnType);
	}

	public List<ArgumentModel> getArguments() {
		return Arrays.asList(args);
	}


	public Optional<Sort> getReturnSort() {
		return Z3Utils.typeBindingToSort(smt.ctx, method.binding.returnType);
	}

	public Optional<Sort[]> getArgumentSorts() {
		var sorts = new Sort[args.length];
		for (int i = 0; i < args.length; i++) {
			var type = args[i].getType();
			if (!type.hasSort()) return Optional.empty();
			sorts[i] = type.toSort();
		}

		return Optional.of(sorts);
	}

	@Override
	public String toString() {
		return String.valueOf(method.selector);
	}
}
