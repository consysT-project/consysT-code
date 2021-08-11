package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import de.tuda.stg.consys.invariants.subset.ProgramModel;

public class VoidModel extends BaseTypeModel<Sort> {

	private final Sort sort;
	
	VoidModel(ProgramModel smt) {
		super(smt);
		sort = model.ctx.mkUninterpretedSort("T_VOID");

		var v = model.ctx.mkFreshConst("v", sort);

		//TODO: How to say that a type has no values?
//		model.solver.add(
//				model.ctx.mkNot(
//					model.ctx.mkExists(new Expr[] { v }, model.ctx.mkEq(v, v), 1, null, null, null, null)
//				)
//		);
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
