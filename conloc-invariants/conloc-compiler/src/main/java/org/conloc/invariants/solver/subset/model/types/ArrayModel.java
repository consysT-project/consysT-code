package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import org.conloc.invariants.solver.subset.model.ProgramModel;
import org.conloc.invariants.solver.subset.utils.Lazy;


public class ArrayModel<ESort extends Sort, EType extends TypeModel<ESort>> extends BaseTypeModel<ArraySort<IntSort, ESort>> {

	private final EType valueType;

	private final Lazy<ArraySort<IntSort, ESort>> cached;

	protected ArrayModel(ProgramModel smt, EType valueType) {
		super(smt);
		this.valueType = valueType;
		this.cached = Lazy.make(() -> smt.ctx.mkArraySort(smt.ctx.getIntSort(), valueType.toSort()));
	}

	@Override
	public ArraySort<IntSort, ESort> toSort() {
		return cached.get();
	}
}
