package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

public class ArrayModel<ESort extends Sort, EType extends TypeModel<ESort>> extends BaseTypeModel<ArraySort<IntSort, ESort>> {

	private final EType valueType;

	private final Lazy<ArraySort<IntSort, ESort>> sort;

	protected ArrayModel(ProgramModel smt, EType valueType) {
		super(smt);
		this.valueType = valueType;
		this.sort = Lazy.make(() -> smt.ctx.mkArraySort(smt.ctx.getIntSort(), valueType.toSort()));
	}

	@Override
	public ArraySort<IntSort, ESort> toSort() {
		return sort.get();
	}
}
