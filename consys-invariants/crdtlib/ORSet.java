package de.tuda.stg.consys.invariants.crdtlib;
//  Observed-Remove Set CRDT (Add wins Sets also)

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.utils.InvariantUtils.replicaId;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import static com.google.common.base.Preconditions.checkNotNull;
import javax.annotation.Nullable;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;

@ReplicatedModel public class ORSet<T> {

    public final Multimap<T, UUID> elements = LinkedHashMultimap.create();
    public final Multimap<T, UUID> tombstones = LinkedHashMultimap.create();


    /* Constructor */
    /*@
    @ ensures elements.isEmpty();
    @ ensures tombstones.isEmpty();
    @*/
    public ORSet() {

    }


    /*@
    @ assignable elements;
    @ ensures elements.containsKey(value);
    @ ensures (\exists UUID u; \old(elements.containsValue(u)) == false; elements.containsValue(u));
    @ ensures (\forall UUID u; \old(elements.containsValue(u)) == false && elements.containsValue(u); (\forall UUID u2; \old(elements.containsValue(u2)) == false && elements.containsValue(u2); u2.equals(u)) );
    @ ensures (\forall UUID u; \old(elements.containsValue(u)); elements.containsValue(u));
    @ ensures (\forall T elem; elem.equals(value) == false; elements.get(elem).equals(\old(elements.get(elem))));
    @*/
    public Void add(final T value) {
        checkNotNull(value);
        UUID uuid = UUID.randomUUID();
        elements.put(value, uuid);
        return null;
    }

    /*@
    @ assignable elements, tombstones;
    @ ensures elements.containsKey(value) == false;
    @ ensures (\forall T elem; elem.equals(value) == false; elements.get(elem).equals(\old(elements.get(elem))));
    @ ensures (\forall UUID u; \old(elements.get(value)).contains(u); tombstones.containsValue(u));
    @ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
    @ ensures (\forall UUID u; tombstones.containsValue(u); \old(elements.get(value)).contains(u) || \old(tombstones.containsValue(u)) );
    @*/
    public Void remove(final T value) {
        checkNotNull(value);
        this.tombstones.putAll(value, elements.get(value));
        elements.removeAll(value);
        return null;
    }


    /*@
    @ assignable \nothing;
    @ ensures \result == elements.containsKey(value);
    @*/
    public boolean contains(final T value) {
        checkNotNull(value);
        return this.elements.containsKey(value);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == elements.isEmpty();
    @*/
    public boolean isEmpty() {
        return elements.isEmpty();
    }

    /*@
    @ assignable \nothing;
    @ ensures (\forall T elem; \result.contains(elem); elements.containsKey(elem));
    @ ensures (\forall T elem; elements.containsKey(elem); \result.contains(elem));
    @*/
    public ImmutableSet<T> getValue() {
        return ImmutableSet.copyOf(elements.keySet());
    }

    /*@
    @ ensures (\forall UUID u; (\old(this.elements.containsValue(u)) || other.elements.containsValue(u)) && \old(this.tombstones.containsValue(u)) == false && other.tombstones.containsValue(u) == false ; elements.containsValue(u) );
    @ ensures (\forall UUID u; elements.containsValue(u); (\old(this.elements.containsValue(u)) || other.elements.containsValue(u)) && \old(this.tombstones.containsValue(u)) == false && other.tombstones.containsValue(u) == false );
    @ ensures (\forall UUID u; \old(this.tombstones.containsValue(u)) || other.tombstones.containsValue(u); tombstones.containsValue(u));
    @ ensures (\forall UUID u; tombstones.containsValue(u); \old(this.tombstones.containsValue(u)) || other.tombstones.containsValue(u));
    @*/
    public Void merge(final ORSet<T> other) {
        this.elements.putAll(other.elements);
        this.tombstones.putAll(other.tombstones);
        this.elements.removeAll(this.tombstones);
        return null;
    }

}
