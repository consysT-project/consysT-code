package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

public class ReplicatedClassModel extends BaseClassModel {



	// Merge Method
	protected MergeMethodModel mergeMethod;


	public ReplicatedClassModel(ProgramModel model, JmlTypeDeclaration jmlType, boolean initialize) {
		super(model, jmlType, initialize);

		if (initialize) {
			initializeMergeMethod();
		}
	}

	void initializeMergeMethod() {
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

				// Handle merge methods here.
				if (methodIsMerge(method.binding)) {
					if (mergeMethodTemp != null)
						throw new IllegalArgumentException("double merge method: " + jmlMethod);

					mergeMethodTemp = new MergeMethodModel(this.model, this, jmlMethod);
					continue;
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
