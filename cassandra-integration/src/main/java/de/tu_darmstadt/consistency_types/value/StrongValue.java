package de.tu_darmstadt.consistency_types.value;

import de.tu_darmstadt.consistency_types.checker.qual.Strong;

import java.io.Serializable;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public interface StrongValue<V extends @Strong Serializable> extends DatabaseValue<V> {


}
