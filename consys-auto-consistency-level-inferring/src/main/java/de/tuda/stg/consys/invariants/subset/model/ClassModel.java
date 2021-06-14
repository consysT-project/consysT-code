package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Map;

public class ClassModel {

	private final Context ctx;

	private final String className;

	// Stores all virtual fields of the class
	private final Map<String, FieldModel> classFields;
	// Stores all static final fields as constants for usage in formulas
	private final Map<String, ConstantModel> classConstants;

	// Z3 Sort to represent states of this class.
	private final TupleSort classSort;

	private ClassModel(Context ctx, String className, Map<String, FieldModel> classFields, Map<String, ConstantModel> classConstants) {
		this.ctx = ctx;
		this.className = className;
		this.classFields = classFields;
		this.classConstants = classConstants;


		// Create a new type for states of this class.
		String[] fieldNames = new String[classFields.size()];
		Sort[] fieldSorts =  new Sort[classFields.size()];
		int i = 0;
		for (FieldModel field : classFields.values()) {
			fieldNames[i] = field.getName();
			fieldSorts[i] = field.getSort();
			i++;
		}
		this.classSort = ctx.mkTupleSort(
				ctx.mkSymbol("state_" + className),
				Z3Utils.mkSymbols(ctx, fieldNames), fieldSorts);

	}

	public static ClassModel parseJMLDeclaration(Context ctx, JmlTypeDeclaration jmlType) {

		String className = String.valueOf(jmlType.name);

		/* Parse fields and constants */
		Map<String, FieldModel> classFields = Maps.newHashMap();
		Map<String, ConstantModel> classConstants = Maps.newHashMap();

		for (FieldDeclaration field : jmlType.fields) {
			//Decide whether field is constant or class field
			if (field.isStatic() && field.binding.isFinal()) {
				// Handle constants
				String fieldName = String.valueOf(field.name);
				Sort sort = Z3Utils.typeReferenceToSort(ctx, field.type);

				//TODO: Handle constants
				Expr initialValue = null;
						//formulaGenerator.visitExpression(field.initialization, internalScope);

				if (initialValue == null)
					throw new IllegalStateException("Constant value must be initialized directly!");

				ConstantModel<Sort> constant = new ConstantModel<>(fieldName, sort, initialValue);
				classConstants.put(fieldName, constant);

			} else if (field.isStatic()) {
				// Static fields are not supported
				throw new IllegalStateException("Non-final static fields are unsupported.");
			} else {
				// virtual fields
				// name of the field
				String fieldName = String.valueOf(field.name);
				// sort of the field
				Sort sort = Z3Utils.typeReferenceToSort(ctx, field.type);
			}

			// constant need to be initialized immediately
		}

		return new ClassModel(ctx, className, classFields, classConstants);
	}

}
