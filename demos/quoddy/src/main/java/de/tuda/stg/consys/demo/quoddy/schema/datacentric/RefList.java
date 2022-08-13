package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

/**
 * Wrapper for java.util.List to be used for replicated lists,
 * since the jdk classes lack @SideEffectFree annotations.
 */
public class RefList<E> implements Serializable {
    private final List<E> underlying = new LinkedList<>();

    public void add(int index, E value) {
        underlying.add(index, value);
    }

    public void add(E value) {
        underlying.add(value);
    }

    @SideEffectFree
    public List<E> subList(int from, int to) {
        return underlying.subList(from, to);
    }

    @SideEffectFree
    public E get(int index) {
        return underlying.get(index);
    }

    @SideEffectFree
    public boolean isEmpty() {
        return underlying.isEmpty();
    }

    @SideEffectFree
    public int size() {
        return underlying.size();
    }

    public List<E> getUnderlying() {
        return underlying;
    }
}
