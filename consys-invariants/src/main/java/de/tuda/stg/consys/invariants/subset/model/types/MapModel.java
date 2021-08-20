package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;

public class MapModel<KSort extends Sort, VSort extends Sort, KType extends TypeModel<KSort>, VType extends TypeModel<VSort>> extends BaseTypeModel<ArraySort<KSort, VSort>> {

	private final Lazy<ArraySort<KSort, VSort>> sort;

	protected MapModel(ProgramModel model, KType keyType, VType valueType) {
		super(model);
		this.sort = Lazy.make(() -> model.ctx.mkArraySort(keyType.toSort(), valueType.toSort()));
	}

	@Override
	public ArraySort<KSort, VSort> toSort() {
		return sort.get();
	}
}
