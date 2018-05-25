package de.tu_darmstadt.consistency_types.store;

import de.tu_darmstadt.consistency_types.checker.qual.PolyConsistent;

/**
 * Created on 24.05.18.
 *
 * @author Mirko Köhler
 */
public interface Handle<T> {

	void set(T value);

	T get();
}
