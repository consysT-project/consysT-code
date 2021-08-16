package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlAbstractMethodDeclaration;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public abstract class AbstractMethodModel<Decl extends AbstractMethodDeclaration & JmlAbstractMethodDeclaration> {

	protected final ProgramModel model;
	protected final BaseClassModel clazz;
	protected final Decl method;

	protected final ArgumentModel[] args;

	public AbstractMethodModel(ProgramModel model, BaseClassModel clazz, Decl method) {
		this.model = model;
		this.clazz = clazz;
		this.method = method;

		if (method.arguments == null) {
			this.args = new ArgumentModel[0];
		} else {
			this.args = Arrays.stream(method.arguments)
					.map(arg -> new ArgumentModel(model, arg))
					.toArray(ArgumentModel[]::new);
		}
	}

	public Optional<Expression> getJmlPrecondition() {
		if (method.getSpecification() == null) return Optional.empty();
		return Optional.of(method.getSpecification().getPrecondition());
	}

	public Optional<Expression> getJmlPostcondition() {
		if (method.getSpecification() == null) return Optional.empty();
		return Optional.of(method.getSpecification().getPostcondition());
	}

	public String getName() {
		return String.valueOf(JDTUtils.nameOfClass(method.binding.declaringClass)) + "." + String.valueOf(method.binding.selector);
	}

	public MethodBinding getBinding() {
		return method.binding;
	}

	public Optional<ArgumentModel> getArgument(Reference arg) {
		return Z3Utils.findReferenceInArray(args, arg, ArgumentModel::getBinding);
	}

	public boolean returnsVoid() {
		return TypeBinding.VOID.equals(method.binding.returnType);
	}

	public List<ArgumentModel> getArguments() {
		return Arrays.asList(args);
	}

	public TypeModel<?> getReturnType() {
		return model.types.typeFor(method.binding.returnType);
	}

	public List<TypeModel<?>> getArgumentTypes() {
		return getArguments().stream().map(VariableModel::getType).collect(Collectors.toList());
	}

	@Override
	public String toString() {
		return String.valueOf(method.selector);
	}
}
