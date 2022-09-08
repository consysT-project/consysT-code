package de.tuda.stg.consys.invariants.solver.subset.model;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Optional;

public class ReplicatedClassModel extends BaseClassModel {

	// Merge Method
	protected MergeMethodModel mergeMethod;

	private boolean mergeIsInitialized = false;


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

		mergeIsInitialized = true;
	}



	@Override
	public Optional<MethodModel> getMethod(MethodBinding binding) {
		if (binding == getMergeMethod().getBinding()) {
			return Optional.of(getMergeMethod());
		}

		return super.getMethod(binding);
	}

	public MergeMethodModel getMergeMethod() {
		if (!mergeIsInitialized) throw new IllegalStateException("merge has not been initialized");
		return mergeMethod;
	}




}
