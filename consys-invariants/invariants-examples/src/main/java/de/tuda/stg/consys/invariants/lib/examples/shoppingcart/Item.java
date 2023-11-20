package de.tuda.stg.consys.invariants.lib.examples.shoppingcart;

import de.tuda.stg.consys.annotations.invariants.DataModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;

@DataModel
public class Item {

	private final String name;

	public Item(String name) {
		this.name = name;
	}

	@Override
	@WeakOp public int hashCode() {
		return name.hashCode();
	}

	@Override
	@WeakOp public boolean equals(Object obj) {
		return obj instanceof Item && ((Item) obj).name.equals(name);
	}
}
