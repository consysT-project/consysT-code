package de.tuda.stg.consys.invariants.solver.subset.model;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.TupleSort;
import de.tuda.stg.consys.logging.Logger;
import de.tuda.stg.consys.invariants.solver.subset.parser.BaseExpressionParser;
import de.tuda.stg.consys.invariants.solver.subset.parser.ExpressionParser;
import de.tuda.stg.consys.invariants.solver.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.solver.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
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
	private FieldModel[] classFields;
	// Stores all static final fields as constants for usage in formulas
	private ConstantModel[] classConstants;

	// Methods
	private MethodModel[] classMethods;
	// Constructors
	private ConstructorModel[] classConstructors;

	// Z3 Sort to represent states of this class.
	private TupleSort classSort;

	private boolean fieldsInitialized = false;
	private boolean sortInitialized = false;
	private boolean methodsInitialized = false;


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

		methodsInitialized = true;
	}

	void initializeSort() {
		/* Create the z3 sort for states of this class. */
		String[] fieldNames = new String[this.classFields.length];
		Sort[] fieldSorts =  new Sort[this.classFields.length];

		for (int i = 0; i < this.classFields.length; i++) {
			FieldModel field = this.classFields[i];
			fieldNames[i] = field.getName();
			fieldSorts[i] = field.getType().getSort()
					.orElseThrow(() -> new IllegalArgumentException("field type cannot be translated to z3: " + field));
		}

		var sortName = model.config.SOLVER__SIMPLE_NAMES ?
				this.model.ctx.mkSymbol("T_" + JDTUtils.simpleNameOfClass(getBinding())) :
				this.model.ctx.mkSymbol("T_CLASS_" + getClassName());

		this.classSort = this.model.ctx.mkTupleSort(
				sortName,
				Z3Utils.mkSymbols(this.model.ctx, fieldNames), fieldSorts);

		FuncDecl<?>[] accessors = classSort.getFieldDecls();
		for (int i = 0; i < this.classFields.length; i++) {
			this.classFields[i].initAccessor(accessors[i]);
		}

		sortInitialized = true;
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

		fieldsInitialized = true;
	}

	public SourceTypeBinding getBinding() {
		return jmlType.binding;
	}

	public String getClassName() {
		return JDTUtils.nameOfClass(jmlType.binding);
	}

	private FieldModel[] getClassFields() {
		if (!fieldsInitialized) throw new IllegalStateException("fields have not been initialized");
		return classFields;
	};
	// Stores all static final fields as constants for usage in formulas
	private ConstantModel[] getClassConstants() {
		if (!fieldsInitialized) throw new IllegalStateException("fields have not been initialized");
		return classConstants;
	}

	private MethodModel[] getClassMethods() {
		if (!methodsInitialized) throw new IllegalStateException("methods have not been initialized");
		return classMethods;
	}

	private ConstructorModel[] getClassConstructors() {
		if (!methodsInitialized) throw new IllegalStateException("methods have not been initialized");
		return classConstructors;
	}

	public Optional<FieldModel> getField(FieldBinding binding) {
		return Z3Utils.findBindingInArray(getClassFields(), JDTUtils.erase(binding), FieldModel::getBinding);
	}

	public Optional<MethodModel> getMethod(MethodBinding binding) {
		return Z3Utils.findBindingInArray(getClassMethods(), JDTUtils.erase(binding), AbstractMethodModel::getBinding);
	}

	public Optional<ConstantModel> getConstant(FieldBinding binding) {
		return Z3Utils.findBindingInArray(getClassConstants(), JDTUtils.erase(binding), ConstantModel::getBinding);
	}

	public Iterable<MethodModel> getMethods() {
		return Arrays.asList(getClassMethods());
	}

	public Iterable<ConstructorModel> getConstructors() {
		return Arrays.asList(getClassConstructors());
	}

	public Iterable<FieldModel> getFields() {
		return Arrays.asList(getClassFields());
	}

	public JmlTypeDeclaration getJmlType() {
		return jmlType;
	}


	public TupleSort getClassSort() {
		if (!sortInitialized) throw new IllegalStateException("sort has not been initialized");
		return classSort;
	}

	public Expr toFreshConst(String name) {
		return model.ctx.mkFreshConst(name, getClassSort());
	}


	protected boolean methodIsMerge(MethodBinding binding) {
		return JDTUtils.methodMatchesSignature(this.getBinding(), binding, false,
				JDTUtils.nameOfClass(jmlType.binding),
				"merge",
				JDTUtils.nameOfClass(jmlType.binding));
	}

}
