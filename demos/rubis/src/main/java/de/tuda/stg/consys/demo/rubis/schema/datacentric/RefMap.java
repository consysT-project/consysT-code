package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.checker.qual.Strong;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * Wrapper for java.util.Map to be used for replicated maps,
 * since the jdk classes lack @SideEffectFree annotations.
 */
public @Strong class RefMap<K, V> implements Serializable {
    private final Map<K, V> underlying = new HashMap<>();

    public void put(K key, V value) {
        underlying.put(key, value);
    }

    public void putIfAbsent(K key, V value) {
        underlying.putIfAbsent(key, value);
    }

    public V remove(K key) {
        return underlying.remove(key);
    }

    @SideEffectFree
    public V get(K key) {
        return underlying.get(key);
    }

    @SideEffectFree
    public Collection<V> values() {
        return underlying.values();
    }

    @SideEffectFree
    public @Strong boolean isEmpty() {
        return (@Strong boolean) underlying.isEmpty();
    }
}
