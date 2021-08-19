package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.Z3Utils;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Optional;

public class ReplicatedClassModel extends BaseClassModel {

	// Merge Method
	protected MergeMethodModel mergeMethod;


	public ReplicatedClassModel(ProgramModel model, JmlTypeDeclaration jmlType, boolean initialize) {
		super(model, jmlType, initialize);
	}

	@Override
	void initializeMethods() {
		super.initializeMethods();

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

	@Override
	public Optional<MethodModel> getMethod(MethodBinding binding) {
		//TODO: Is there any special case that we have to note here?
		if (binding == mergeMethod.getBinding()) {
			return Optional.of(mergeMethod);
		}

		return super.getMethod(binding);
	}

	public MergeMethodModel getMergeMethod() {
		return mergeMethod;
	}




}
