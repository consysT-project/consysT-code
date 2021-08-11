package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;

public class RefModel extends BaseTypeModel<Sort> {

	private final Lazy<Sort> backUpSort;
	private final ReferenceBinding refBinding;

	RefModel(ProgramModel model, ReferenceBinding refBinding) {
		super(model);
		this.refBinding = refBinding;
		this.backUpSort = Lazy.make(() -> model.ctx.mkUninterpretedSort("T_UN_" + String.valueOf(refBinding.shortReadableName())));
	}

	@Override
	public boolean hasSort() {
		return true;
	}

	@Override
	public Sort toSort() {
		var maybeModel = model.getModelForClass(refBinding);

		if (maybeModel.isPresent()) {
			return maybeModel.get().getClassSort();
		}

		return backUpSort.get();
	}




}
