package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.conloc.invariants.solver.subset.utils.Lazy;

public class CollectionModel<VSort extends Sort, VType extends TypeModel<VSort>> extends BaseTypeModel<ArraySort<VSort, IntSort>> {

	private final VType valueType;

	private final Lazy<ArraySort<VSort, IntSort>> sort;

	protected CollectionModel(ProgramModel model, VType valueType) {
		super(model);
		this.valueType = valueType;
		this.sort = Lazy.make(() -> model.ctx.mkArraySort(valueType.toSort(), model.ctx.getIntSort()));
	}

	@Override
	public ArraySort<VSort, IntSort> toSort() {
		return sort.get();
	}
}
