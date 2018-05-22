package de.tu_darmstadt.consistency_types.value;

import de.tu_darmstadt.consistency_types.checker.qual.Weak;

import java.io.Serializable;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public interface WeakValue<V extends @Weak Serializable> extends DatabaseValue<V> {


}
