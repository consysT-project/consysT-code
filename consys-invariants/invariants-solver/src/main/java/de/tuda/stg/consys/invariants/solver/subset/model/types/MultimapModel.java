package de.tuda.stg.consys.invariants.solver.subset.model.types;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.solver.subset.utils.Lazy;

public class MultimapModel<KSort extends Sort, VSort extends Sort, KType extends TypeModel<KSort>, VType extends TypeModel<VSort>>
		extends BaseTypeModel<ArraySort<KSort, ArraySort<VSort, IntSort>>> {

	private final Lazy<ArraySort<KSort, ArraySort<VSort, IntSort>>> sort;

	protected MultimapModel(ProgramModel model, KType keyType, VType valueType) {
		super(model);
		this.sort = Lazy.make(() ->
				model.ctx.mkArraySort(keyType.toSort(),
				model.ctx.mkArraySort(valueType.toSort(), model.ctx.getIntSort()))
		);
	}

	@Override
	public ArraySort<KSort, ArraySort<VSort, IntSort>> toSort() {
		return sort.get();
	}
}
