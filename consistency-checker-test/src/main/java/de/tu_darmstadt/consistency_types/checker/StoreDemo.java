package de.tu_darmstadt.consistency_types.checker;

import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.store.Handle;
import de.tu_darmstadt.consistency_types.store.Store;
import de.tu_darmstadt.consistency_types.store.impl.local.MapStore;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public class StoreDemo {

	public static void main(String[] args) throws Exception {

		System.out.println("Start");

		Store store = new MapStore();

		Handle<@Strong Integer> a = store.obtain(1, Strong.class);
		a.set(42);

		Handle<@Weak Integer> b = store.obtain(2, Weak.class);
		b.set(23);

		//Error: leakage from weak to strong
		//a.set(b.get());

		//Error: implicit flow
		if (b.get() == 23) {
		//	a.set(1);
		}
	}
}
