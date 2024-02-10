package de.tuda.stg.consys.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.utils.JDTUtils;
import org.eclipse.jdt.internal.compiler.lookup.MissingTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;

public class MissingModel extends BaseTypeModel<Sort> {

	private final Sort sort;
	private final MissingTypeBinding missingBinding;

	MissingModel(ProgramModel model, MissingTypeBinding missingBinding) {
		super(model);
		this.missingBinding = missingBinding;
		this.sort = model.ctx.mkUninterpretedSort("T_MISSING_" + JDTUtils.simpleNameOfClass(this.missingBinding));
	}

	public ReferenceBinding getMissingBinding() {
		return missingBinding;
	}

	@Override
	public boolean hasSort() {
		return true;
	}

	@Override
	public Sort toSort() {
		return sort;
	}




}
