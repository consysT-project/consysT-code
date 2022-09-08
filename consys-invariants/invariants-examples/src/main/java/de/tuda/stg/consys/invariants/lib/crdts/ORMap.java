package de.tuda.stg.consys.invariants.lib.crdts;


import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.util.UUID;
import java.util.Map;
import java.util.HashMap;

import static com.google.common.base.Preconditions.checkNotNull;

@ReplicatedModel public class ORMap<K, V extends Mergeable<V>> implements Mergeable<ORMap<K,V>> {
    //@ public invariant (\forall K k; underlying.containsKey(k); elements.containsKey(k));
    //@ public invariant (\forall K k; elements.containsKey(k); underlying.containsKey(k));

    public final Map<K, V> underlying = new HashMap<K, V>();
    public final Multimap<K, UUID> elements = LinkedHashMultimap.create();
    public final Multimap<K, UUID> tombstones = LinkedHashMultimap.create();


    //@ ensures underlying.isEmpty();
    //@ ensures elements.isEmpty();
    //@ ensures tombstones.isEmpty();
    public ORMap() {

    }

    /*@
    @ assignable elements, underlying;
    @
    @ ensures underlying.containsKey(key);
    @ ensures (\forall K k0; !k0.equals(key); underlying.get(k0).equals(\old(underlying.get(k0))));
    @ ensures (\forall K k1; \old(underlying).containsKey(k1); underlying.containsKey(k1)); // TODO: redundant?
    @ ensures underlying.size() == \old(underlying).size() || underlying.size() == \old(underlying).size() + 1;
    @
    @ ensures elements.containsKey(key);
    @ ensures (\exists UUID u; \old(elements.containsValue(u)) == false; elements.containsValue(u));
    @ ensures (\forall UUID u; \old(elements.containsValue(u)) == false && elements.containsValue(u); (\forall UUID u2; \old(elements.containsValue(u2)) == false && elements.containsValue(u2); u2.equals(u)) );
    @ ensures (\forall UUID u; \old(elements.containsValue(u)); elements.containsValue(u));
    @ ensures (\forall K elem; elem.equals(key) == false; elements.get(elem).equals(\old(elements.get(elem))));
    @*/
    public void put(K key, V value) {
        checkNotNull(key);
        UUID uuid = UUID.randomUUID();
        elements.put(key, uuid);
        underlying.put(key, value);
    }

    /*@
    @ assignable elements, tombstones, underlying;
    @
    @ ensures !underlying.containsKey(key);
    @ ensures (\forall K k0; !k0.equals(key); underlying.get(k0).equals(\old(underlying.get(k0))));
    @ ensures (\forall K k1; !k1.equals(key) && \old(underlying).containsKey(k1); underlying.containsKey(k1)); // TODO: redundant?
    @
    @ ensures !elements.containsKey(key);
    @ ensures (\forall K elem; elem.equals(key) == false; elements.get(elem).equals(\old(elements.get(elem))));
    @ ensures (\forall UUID u; \old(elements.get(key)).contains(u); tombstones.containsValue(u));
    @ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
    @ ensures (\forall UUID u; tombstones.containsValue(u); \old(elements.get(key)).contains(u) || \old(tombstones.containsValue(u)) );
    @*/
    public void remove(K key) {
        checkNotNull(key);
        this.tombstones.putAll(key, elements.get(key));
        elements.removeAll(key);
        underlying.remove(key);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.containsKey(key);
    public boolean containsKey(K key){
        checkNotNull(key);
        return underlying.containsKey(key);
    }

    //@ assignable \nothing;
    //@ ensures \result == elements.isEmpty();
    public boolean isEmpty() {
        return elements.isEmpty();
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.get(key); // TODO: not pure?
    public V get(K key) {
        return underlying.get(key);
    }

    /*@
    @ ensures (\forall K k0; \old(underlying).containsKey(k0) || other.underlying.containsKey(k0); underlying.containsKey(k0));
    @ ensures (\forall K k1; underlying.containsKey(k1); \old(underlying).containsKey(k1) || other.underlying.containsKey(k1));
    @*/
    public Void merge(ORMap<K, V> other) {
        for (K k : other.underlying.keySet()) {
            if (this.underlying.containsKey(k)) {
                V elem = this.underlying.get(k);
                elem.merge(other.underlying.get(k));
                this.underlying.put(k, elem);
            } else {
                this.underlying.put(k, other.underlying.get(k));
            }
        }

        this.elements.putAll(other.elements);
        this.tombstones.putAll(other.tombstones);

        for (K key : this.elements.keySet()) {
            for (UUID uuid : this.tombstones.get(key)) {
                this.elements.remove(key, uuid);
            }
            if (!this.elements.containsKey(key))
                this.underlying.remove(key);
        }
        return null;
    }
}
