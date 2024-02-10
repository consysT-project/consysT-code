package de.tuda.stg.consys.invariants.solver.subset.model.types;

import com.microsoft.z3.SetSort;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.utils.Lazy;

public class SetModel<VSort extends Sort, VType extends TypeModel<VSort>> extends BaseTypeModel<SetSort<VSort>> {

	private final VType valueType;

	private final Lazy<SetSort<VSort>> sort;

	protected SetModel(ProgramModel model, VType valueType) {
		super(model);
		this.valueType = valueType;
		this.sort = Lazy.make(() -> model.ctx.mkSetSort(valueType.toSort()));
	}

	@Override
	public SetSort<VSort> toSort() {
		return sort.get();
	}
}
