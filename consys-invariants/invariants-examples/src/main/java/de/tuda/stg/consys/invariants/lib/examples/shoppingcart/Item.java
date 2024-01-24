package de.tuda.stg.consys.invariants.lib.examples.shoppingcart;

import de.tuda.stg.consys.annotations.invariants.DataModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.io.Serializable;

@DataModel
public class Item implements Serializable {

	private final String name;

	public Item(String name) {
		this.name = name;
	}

	@Override
	 public int hashCode() {
		return name.hashCode();
	}

	@Override
	 public boolean equals(Object obj) {
		return obj instanceof Item && ((Item) obj).name.equals(name);
	}
}
