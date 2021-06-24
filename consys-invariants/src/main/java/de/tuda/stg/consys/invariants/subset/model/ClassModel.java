package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import de.tuda.stg.consys.invariants.subset.parser.BaseExpressionParser;
import de.tuda.stg.consys.invariants.subset.parser.ExpressionParser;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.*;

public class ClassModel {

	private final Context ctx;
	// The underlying jml type for this declaration
	private final JmlTypeDeclaration jmlType;

	// Stores all virtual fields of the class
	private final FieldModel[] classFields;
	// Stores all static final fields as constants for usage in formulas
	private final ConstantModel[] classConstants;

	// Methods
	private final MethodModel[] classMethods;
	// Merge Method
	private final MergeMethodModel mergeMethod;
	// Constructors
	private final ConstructorModel[] classConstructors;

	// Z3 Sort to represent states of this class.
	private final TupleSort classSort;


	public ClassModel(Context ctx, JmlTypeDeclaration jmlType) {
		this.ctx = ctx;
		this.jmlType = jmlType;

		/* Parse fields and constants */
		List<FieldModel> classFieldsTemp = new ArrayList(jmlType.fields.length);
		List<ConstantModel> classConstantsTemp = new ArrayList(jmlType.fields.length);

		for (int i = 0; i < jmlType.fields.length; i++) {
			FieldDeclaration field = jmlType.fields[i];

			//Decide whether field is constant or class field
			if (field.isStatic() && field.binding.isFinal()) {
				// Handle constants
				if (field.initialization == null)
					throw new IllegalStateException("Constant value must be initialized directly for field " + field);

				ExpressionParser parser = new BaseExpressionParser(ctx);
				Expr initialValue = parser.parseExpression(field.initialization);

				classConstantsTemp.add(new ConstantModel(ctx, field, initialValue));

			} else if (field.isStatic()) {
				// Static fields are not supported
				throw new IllegalStateException("Non-final static fields are unsupported.");
			} else {
				classFieldsTemp.add(new FieldModel(ctx, field, null /* accessor is initialized later. */));
			}
		}
		this.classFields = classFieldsTemp.toArray(FieldModel[]::new);
		this.classConstants = classConstantsTemp.toArray(ConstantModel[]::new);

		/* Create the z3 sort for states of this class. */
		String[] fieldNames = new String[this.classFields.length];
		Sort[] fieldSorts =  new Sort[this.classFields.length];

		for (int i = 0; i < this.classFields.length; i++) {
			FieldModel field = this.classFields[i];
			fieldNames[i] = field.getName();
			fieldSorts[i] = field.getSort();
		}

		this.classSort = ctx.mkTupleSort(
				ctx.mkSymbol("state_" + getClassName()),
				Z3Utils.mkSymbols(ctx, fieldNames), fieldSorts);

		FuncDecl<?>[] accessors = classSort.getFieldDecls();
		for (int i = 0; i < this.classFields.length; i++) {
			this.classFields[i].initAccessor(accessors[i]);
		}


		/* Parse methods */
		List<MethodModel> classMethods = new ArrayList<>(jmlType.methods.length);
		List<ConstructorModel> classConstructors = new ArrayList<>(jmlType.methods.length);
		MergeMethodModel mergeMethodTemp = null;

		for (int i = 0; i < jmlType.methods.length; i++) {
			AbstractMethodDeclaration method = jmlType.methods[i];

			if (method.isClinit()) {
				// TODO: Handle clinit
			} else if (method.isConstructor()) {
				classConstructors.add(new ConstructorModel(ctx, (JmlConstructorDeclaration) method));
			} else if (method.isStatic() || method.isAbstract()) {
				throw new IllegalStateException("Static and abstract methods are unsupported: " + method);
			} else if (method instanceof JmlMethodDeclaration) {
				JmlMethodDeclaration jmlMethod = (JmlMethodDeclaration) method;
				if ("merge".equals(String.valueOf(jmlMethod.selector))) {
					if (jmlMethod.arguments.length == 1 && jmlMethod.arguments[0].binding.type.equals(jmlType.binding)
							&& jmlMethod.binding.returnType.equals(TypeBinding.VOID)) {
						if (mergeMethodTemp != null)
							throw new IllegalArgumentException("double merge method: " + jmlMethod);

						mergeMethodTemp = new MergeMethodModel(ctx, jmlMethod);
					} else {
						System.err.println("WARNING! Method with name `merge` is not a valid merge method.");
						classMethods.add(new MethodModel(ctx, jmlMethod));
					}
				} else {
					classMethods.add(new MethodModel(ctx, jmlMethod));
				}
			} else {
				//TODO: change to sensible defaults.
				throw new IllegalStateException("Only jml method declarations are supported.");
			}
		}

		if (mergeMethodTemp == null) {
			throw new IllegalArgumentException("no merge method found.");
		}

		this.mergeMethod = mergeMethodTemp;
		this.classMethods = classMethods.toArray(MethodModel[]::new);
		this.classConstructors = classConstructors.toArray(ConstructorModel[]::new);

	}


	public String getClassName() {
		return String.valueOf(jmlType.name);
	}

	public TupleSort getClassSort() {
		return classSort;
	}

	public Optional<FieldModel> getField(Reference fieldRef) {
		return Z3Utils.findReferenceInArray(classFields, fieldRef, (field) -> field.getDecl().binding);
	}

	public Optional<FieldModel> getField(FieldBinding binding) {
		return Z3Utils.findBindingInArray(classFields, binding, (field) -> field.getDecl().binding);
	}

	public Optional<MethodModel> getMethod(MethodBinding binding) {
		return Z3Utils.findBindingInArray(classMethods, binding, method -> method.getDecl().binding);
	}

	public Optional<ConstantModel> getConstant(Reference constantRef) {
		return Z3Utils.findReferenceInArray(classConstants, constantRef, (constant) -> constant.getDecl().binding);
	}

	public Iterable<MethodModel> getMethods() {
		return Arrays.asList(classMethods);
	}

	public Iterable<ConstructorModel> getConstructors() {
		return Arrays.asList(classConstructors);
	}

	public Iterable<FieldModel> getFields() {
		return Arrays.asList(classFields);
	}

	public JmlTypeDeclaration getJmlType() {
		return jmlType;
	}

	public MergeMethodModel getMergeMethod() {
		return mergeMethod;
	}


	public Expr getFreshConst(String name) {
		return ctx.mkFreshConst(name, getClassSort());
	}
}
