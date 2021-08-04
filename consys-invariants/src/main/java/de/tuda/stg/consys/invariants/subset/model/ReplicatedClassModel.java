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
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

public class ReplicatedClassModel extends ClassModel {



	// Merge Method
	final MergeMethodModel mergeMethod;


	public ReplicatedClassModel(ProgramModel model, JmlTypeDeclaration jmlType) {
		super(model, jmlType);




		/* Parse merge method */
		MergeMethodModel mergeMethodTemp = null;

		for (int i = 0; i < jmlType.methods.length; i++) {
			AbstractMethodDeclaration method = jmlType.methods[i];

			if (method.isClinit() || method.isConstructor()) {
				// TODO: Handle clinit
			} else if (method.isStatic() || method.isAbstract()) {
				throw new IllegalStateException("Static and abstract methods are unsupported: " + method);
			} else if (method instanceof JmlMethodDeclaration) {
				JmlMethodDeclaration jmlMethod = (JmlMethodDeclaration) method;

				//Check if the method is a merge method.
				if (JDTUtils.methodMatchesSignature(method.binding, false,
						JDTUtils.nameOfClass(jmlType.binding),
						"merge",
						JDTUtils.nameOfClass(jmlType.binding))) {
					if (jmlMethod.arguments.length == 1 && jmlMethod.arguments[0].binding.type.equals(jmlType.binding)
							&& jmlMethod.binding.returnType.equals(TypeBinding.VOID)) {
						if (mergeMethodTemp != null)
							throw new IllegalArgumentException("double merge method: " + jmlMethod);

						mergeMethodTemp = new MergeMethodModel(this.model, this, jmlMethod);
						continue;
					} else {
						Logger.info("method with name \"merge\" is not a valid merge method.");
					}
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

	}


	public MergeMethodModel getMergeMethod() {
		return mergeMethod;
	}




}
