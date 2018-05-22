package de.tu_darmstadt.consistency_types.value;

import de.tu_darmstadt.consistency_types.checker.qual.PolyConsistent;

import java.io.Serializable;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public interface DatabaseValue<V extends Serializable> {

	V read() throws Exception;
	void write(V value) throws Exception;
}
