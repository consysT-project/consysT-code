package de.tuda.stg.consys;

/** Interface for mergeable data types */
public interface Mergeable<T extends Mergeable<T>> {
    Void merge(T other);
}
