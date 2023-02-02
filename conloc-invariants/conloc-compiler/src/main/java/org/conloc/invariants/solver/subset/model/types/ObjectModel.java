package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.conloc.invariants.solver.subset.utils.JDTUtils;
import org.conloc.invariants.solver.subset.utils.Lazy;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;

public class ObjectModel extends BaseTypeModel<Sort> {

	private final Lazy<Sort> backUpSort;
	private final ReferenceBinding refBinding;

	ObjectModel(ProgramModel model, ReferenceBinding refBinding) {
		super(model);
		this.refBinding = refBinding;
		this.backUpSort = Lazy.make(() -> {
			var sortName = model.config.SOLVER__SIMPLE_NAMES ?
					"T_UNRESOLVED_" + JDTUtils.simpleNameOfClass(refBinding):
					"T_CLASS_UNRESOLVED_" + JDTUtils.nameOfClass(refBinding);
			return model.ctx.mkUninterpretedSort(sortName);
		});
	}


	public ReferenceBinding getRefBinding() {
		return refBinding;
	}

	@Override
	public boolean hasSort() {
		return true;
	}

	@Override
	public Sort toSort() {
		var maybeModel = model.getClassModel(refBinding);

		if (maybeModel.isPresent()) {
			return maybeModel.get().getClassSort();
		}

		return backUpSort.get();
	}




}
