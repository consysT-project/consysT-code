package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;

public class MapModel<KSort extends Sort, VSort extends Sort, KType extends TypeModel<KSort>, VType extends TypeModel<VSort>> extends BaseTypeModel<ArraySort<KSort, VSort>> {

	private final VType valueType;

	private final Lazy<ArraySort<KSort, VSort>> sort;

	protected MapModel(ProgramModel smt, KType keyType, VType valueType) {
		super(smt);
		this.valueType = valueType;
		this.sort = Lazy.make(() -> smt.ctx.mkArraySort(keyType.toSort(), valueType.toSort()));
	}

	@Override
	public ArraySort<KSort, VSort> toSort() {
		return sort.get();
	}
}
