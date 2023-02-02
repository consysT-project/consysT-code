package org.conloc;

/** Interface for mergeable data types */
public interface Mergeable<T /* TODO: Can we re-add the following?*//*extends Mergeable<T>*/> {
    Void merge(T other);
}
