package de.tuda.stg.consys.invariants.lib.examples.shoppingcart;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.invariants.lib.crdts.TwoPhaseSet;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;


@ReplicatedModel
public class ShoppingCart {

	private final TwoPhaseSet<Item> items;

	public ShoppingCart() {
		items = new TwoPhaseSet<>();
	}

	//@ ensures stateful( items.add(item) );
	@WeakOp public Void addItem(Item item) {
		items.add(item);
		return null;
	}

	public Void merge(ShoppingCart other) {
		items.merge(other.items);
		return null;
	}
}
