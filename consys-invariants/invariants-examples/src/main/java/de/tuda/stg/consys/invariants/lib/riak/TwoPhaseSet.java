package de.tuda.stg.consys.invariants.lib.riak;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;


import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;



/**
 * Supports both add and remove operations, but only allows for a single remove.
 * 
 */
@ReplicatedModel public class TwoPhaseSet<E> {

	private static final String ADD_TOKEN = "a";
	private static final String REMOVE_TOKEN = "r";

	private final GSet<E> adds;
	private final GSet<E> removals;



	/*@
	@ ensures adds.value().isEmpty();
	@ ensures removals.value().isEmpty();
	@*/
	public TwoPhaseSet() {
		adds = new GSet<E>();
		removals = new GSet<E>();
	}



	/*@
	@ ensures (\forall E val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
	@ ensures (\forall E val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
	@ ensures (\forall E val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
	@ ensures (\forall E val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
	@*/
	public Void merge(TwoPhaseSet<E> other) {
		adds.addAll(other.adds.delegate());
		removals.addAll(other.removals.delegate());

		return null;
	}

	/*@
	@ assignable \nothing;
	@ ensures (\forall E elem; adds.contains(elem) && removals.contains(elem) == false; \result.contains(elem));
	@ ensures (\forall E elem; \result.contains(elem); adds.contains(elem) && removals.contains(elem) == false);
	@*/
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(Sets.difference(this.adds.delegate(), this.removals.delegate()));
	}

	// No need to annotate
	// changed from original: @Override
	public byte[] payload() {
//		try {
//			Map<String, JsonNode> retval = Maps.newHashMap();
//
//			retval.put(ADD_TOKEN, serializer.readTree(adds.payload()));
//			retval.put(REMOVE_TOKEN, serializer.readTree(removals.payload()));
//
//			return serializer.writeValueAsBytes(retval);
//		} catch (IOException ioe) {
//			throw new IllegalStateException("Could not serialize.", ioe);
//		}
		return null;
	}

	/*@
	@ requires (removals.contains(obj) == false);
	@ assignable adds;
	@ ensures adds.contains(obj);
    @ ensures (\forall E elem; \old(adds.contains(elem)); adds.contains(elem));
    @ ensures (\forall E elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
    @ ensures \result == !(\old(adds.contains(obj)));
	@*/
	public boolean add(E obj) {
		if (removals.contains(obj)) {
			throw new IllegalArgumentException(
					"Cannot add to a group that has had the value removed.");
		}
		return adds.add(obj);
	}

	/*@
	@ requires (\forall E elem; col.contains(elem); removals.contains(elem) == false);
	@ assignable adds;
	@ ensures (\forall E elem; col.contains(elem); adds.contains(elem));
    @ ensures (\forall E elem; \old(adds.contains(elem)); adds.contains(elem));
	@ ensures (\forall E elem; adds.contains(elem) && col.contains(elem) == false; \old(adds.contains(elem)));
	@ ensures \result == !(\forall E elem; col.contains(elem); \old(adds.contains(elem)));
	@*/
	public boolean addAll(Set<E> col) {
		Set<E> s = Sets.intersection(removals.delegate(), Sets.newHashSet(col));

		if (s.size() > 0) {
			throw new IllegalArgumentException(String.format(
					"%d Elements have already been removed.", s.size()));
		}

		return adds.addAll(col);
	}

	/*@
	@ assignable removals;
	@ ensures (\forall E elem; adds.contains(elem); removals.contains(elem));
	@*/
	// changed from original: @Override
	public void clear() {
		removals.addAll(adds.delegate());

	}

	/*@
	@ assignable \nothing;
	@ ensures \result == !removals.contains(obj) && adds.contains(obj);
	@*/
	// changed from original: @Override
	public boolean contains(Object obj) {
		return !removals.contains(obj) && adds.contains(obj);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; col.contains(elem); removals.contains(elem) == false) && (\forall E elem; col.contains(elem); adds.contains(elem));
	@*/
	public boolean containsAll(Set<E> col) {
		Set<E> s = Sets.intersection(removals.delegate(), Sets.newHashSet(col));
		return s.isEmpty() && adds.containsAll(col);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; adds.contains(elem); removals.contains(elem));
	@*/
	// changed from original: @Override
	public boolean isEmpty() {
		return removals.containsAll(adds.delegate());
	}

	// No need to annotate
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public Iterator<E> iterator() {
		return this.value().iterator();
	}


	/*@
	@ assignable removals;
	@ ensures removals.contains(obj);
	@ ensures (\forall E elem; \old(removals.contains(elem)); removals.contains(elem));
	@ ensures (\forall E elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
	@ ensures \result == \old(removals.contains(obj)) && !adds.contains(obj);
	@*/
	// changed from original: @Override
	// changed from original: @SuppressWarnings("unchecked")
	public boolean remove(E obj) {
		if (removals.contains(obj) || !adds.contains(obj)) {
			return false;
		}

		removals.add(obj);

		return true;
	}

	// Omitted: requires col.contains(null) == false;
	/*@
	@ requires col.isEmpty() == false;
	@ assignable removals;
	@ ensures (\forall E elem; col.contains(elem) && adds.contains(elem); removals.contains(elem));
    @ ensures (\forall E elem; \old(removals.contains(elem)); removals.contains(elem));
	@ ensures (\forall E elem; removals.contains(elem) && col.contains(elem) == false; \old(removals.contains(elem)));
	@ ensures \result == !(\forall E elem; col.contains(elem); \old(removals.contains(elem)));
	@*/
	// changed from original: @Override
	// changed from original: @SuppressWarnings("unchecked")
	public boolean removeAll(final Set<E> col) {
		checkNotNull(col);
//		checkCollectionDoesNotContainNull(col);
		
		Set<E> input = Sets.newHashSet(col);
		Set<E> intersection = Sets.intersection(this.adds.delegate(), input);
		
		return this.removals.addAll(intersection);
	}

	/*@
	@ requires col.isEmpty() == false;
	@ assignable removals;
	@ ensures (\forall E elem; col.contains(elem) && adds.contains(elem) && \old(removals.contains(elem)) == false; !removals.contains(elem));
	@ ensures (\forall E elem; \old(removals.contains(elem)); removals.contains(elem));
	@ ensures (\forall E elem; removals.contains(elem) && \old(removals.contains(elem)) == false; adds.contains(elem) && col.contains(elem) == false);
	@ ensures \result == (\exists E elem; !col.contains(elem) && this.value().contains(elem); true);
	@*/
	public boolean retainAll(final Collection<E> col) {
		checkNotNull(col);
//		checkCollectionDoesNotContainNull(col);

		Set<E> input = Sets.newHashSet(col);
		Set<E> diff = Sets.difference(this.value(), input);

		return this.removeAll(diff);
	}


	//@ requires false;
	//@ assignable \nothing;
	public int size() {
//		return this.adds.size() - this.removals.size();
		return 0;
	}

	// Previously: ensures \result.equals(this.value().toArray());
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public Object[] toArray() {
		return this.value().toArray();
	}

	// Previously: ensures \result.equals(this.value().toArray(arg));
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public <T> T[] toArray(final T[] arg) {
		return this.value().toArray(arg);
	}


	//@ requires false;
	//@ assignable \nothing;
	public final boolean equals(final Object o) {

		if (!(o instanceof TwoPhaseSet)) {
			return false;
		}

		TwoPhaseSet<?> t = (TwoPhaseSet<?>) o;

		if (this == t) {
			return true;
		} else {
			return this.value().equals(t.value());
		}
	}

	/*@
	@ assignable \nothing;
	@*/
	public int hashCode() {
		return this.value().hashCode();
	}

	/*@
	@ assignable \nothing;
	@*/
	public String toString() {
		return this.value().toString();
	}
}
