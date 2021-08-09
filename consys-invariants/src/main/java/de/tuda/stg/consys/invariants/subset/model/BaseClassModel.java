package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.TupleSort;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.parser.BaseExpressionParser;
import de.tuda.stg.consys.invariants.subset.parser.ExpressionParser;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.SourceTypeBinding;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

public class BaseClassModel {

	protected final ProgramModel model;
	// The underlying jml type for this declaration
	protected final JmlTypeDeclaration jmlType;

	// Stores all virtual fields of the class
	protected FieldModel[] classFields;
	// Stores all static final fields as constants for usage in formulas
	protected ConstantModel[] classConstants;

	// Methods
	protected MethodModel[] classMethods;
	// Constructors
	protected ConstructorModel[] classConstructors;

	// Z3 Sort to represent states of this class.
	private TupleSort classSort;


	public BaseClassModel(ProgramModel model, JmlTypeDeclaration jmlType, boolean initialize) {
		this.model = model;
		this.jmlType = jmlType;

		if (initialize) {
			initializeFields();
			initializeSort();
			initializeMethods();
		}
	}

	void initializeMethods() {
		/* Parse methods */
		List<MethodModel> classMethods = new ArrayList<>(jmlType.methods.length);
		List<ConstructorModel> classConstructors = new ArrayList<>(jmlType.methods.length);

		for (int i = 0; i < jmlType.methods.length; i++) {
			AbstractMethodDeclaration method = jmlType.methods[i];

			if (method.isClinit()) {
				// TODO: Handle clinit
			} else if (method.isConstructor()) {
				classConstructors.add(new ConstructorModel(this.model, this, (JmlConstructorDeclaration) method));
			} else if (method.isStatic() || method.isAbstract()) {
				throw new IllegalStateException("Static and abstract methods are unsupported: " + method);
			} else if (method instanceof JmlMethodDeclaration) {
				JmlMethodDeclaration jmlMethod = (JmlMethodDeclaration) method;

				if (methodIsMerge(method.binding))
					//Do not handle merge methods here.
					continue;

				// If the method is a normal method.
				MethodModel methodModel = new MethodModel(this.model, this, jmlMethod);
				// Creating the method model also creates a function declaration for z3.
				classMethods.add(methodModel);

			} else {
				//TODO: change to sensible defaults.
				throw new IllegalStateException("Only jml method declarations are supported.");
			}
		}

		this.classMethods = classMethods.toArray(MethodModel[]::new);
		this.classConstructors = classConstructors.toArray(ConstructorModel[]::new);
	}

	void initializeSort() {
		/* Create the z3 sort for states of this class. */
		String[] fieldNames = new String[this.classFields.length];
		Sort[] fieldSorts =  new Sort[this.classFields.length];

		for (int i = 0; i < this.classFields.length; i++) {
			FieldModel field = this.classFields[i];
			fieldNames[i] = field.getName();
			fieldSorts[i] = field.getType().getSort()
					.orElseThrow(
							() -> new IllegalArgumentException("field type cannot be translated to z3: " + field)
					);
		}

		this.classSort = this.model.ctx.mkTupleSort(
				this.model.ctx.mkSymbol("state_" + getClassName()),
				Z3Utils.mkSymbols(this.model.ctx, fieldNames), fieldSorts);

		FuncDecl<?>[] accessors = classSort.getFieldDecls();
		for (int i = 0; i < this.classFields.length; i++) {
			this.classFields[i].initAccessor(accessors[i]);
		}
	}

	void initializeFields() {
		/* Parse fields and constants */
		List<FieldModel> classFieldsTemp = new ArrayList(jmlType.fields.length);
		List<ConstantModel> classConstantsTemp = new ArrayList(jmlType.fields.length);

		for (int i = 0; i < jmlType.fields.length; i++) {
			FieldDeclaration field = jmlType.fields[i];

			if (field.binding == null) {
				Logger.warn("field will not be available. no binding for field: " +  String.valueOf(field.name));
				continue;
			}

			//Decide whether field is constant or class field
			if (field.isStatic() && field.binding.isFinal()) {
				// Handle constants
				if (field.initialization == null) {
					// throw new IllegalStateException("Constant value must be initialized directly for field " + field);
					Logger.warn("not possible to use static final field " +  String.valueOf(field.name) +  " as constant. Reason: field was not initialized. Field: " + field);
				} else {
					ExpressionParser parser = new BaseExpressionParser(this.model);
					Expr initialValue = parser.parseExpression(field.initialization);

					classConstantsTemp.add(new ConstantModel(this.model, field, initialValue));
				}

			} else if (field.isStatic()) {
				// Static fields are not supported
				throw new IllegalStateException("Non-final static fields are unsupported.");
			} else {
				classFieldsTemp.add(new FieldModel(this.model, field, null /* accessor is initialized later. */));
			}
		}
		this.classFields = classFieldsTemp.toArray(FieldModel[]::new);
		this.classConstants = classConstantsTemp.toArray(ConstantModel[]::new);
	}

	public SourceTypeBinding getBinding() {
		return jmlType.binding;
	}

	public String getClassName() {
		return JDTUtils.nameOfClass(jmlType.binding);
	}

	public Optional<FieldModel> getField(Reference fieldRef) {
		return Z3Utils.findReferenceInArray(classFields, fieldRef, (field) -> field.getDecl().binding);
	}

	public Optional<FieldModel> getField(FieldBinding binding) {
		return Z3Utils.findBindingInArray(classFields, binding, (field) -> field.getDecl().binding);
	}

	public Optional<MethodModel> getMethod(MethodBinding binding) {
		return Z3Utils.findBindingInArray(classMethods, binding, AbstractMethodModel::getBinding);
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


	public TupleSort getClassSort() {
		return classSort;
	}

	public Expr toFreshConst(String name) {
		return model.ctx.mkFreshConst(name, getClassSort());
	}


	protected boolean methodIsMerge(MethodBinding binding) {
		return JDTUtils.methodMatchesSignature(binding, false,
				JDTUtils.nameOfClass(jmlType.binding),
				"merge",
				JDTUtils.nameOfClass(jmlType.binding));
	}

}
