package com.readytalk.crdt.sets;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.readytalk.crdt.util.CollectionUtils.checkCollectionDoesNotContainNull;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;
import javax.inject.Inject;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/**
 * Supports both add and remove operations, but only allows for a single remove.
 * 
 */
@ReplicatedModel public class TwoPhaseSet<E> implements
		CRDTSet<E, ImmutableSet<E>, TwoPhaseSet<E>> {

	private static final String ADD_TOKEN = "a";
	private static final String REMOVE_TOKEN = "r";

	private final ObjectMapper serializer;
	private final GSet<E> adds;
	private final GSet<E> removals;

	private final TypeReference<Map<String, JsonNode>> ref = new TypeReference<Map<String, JsonNode>>() {

	};

	/*@
	@ ensures adds.value().isEmpty();
	@ ensures removals.value().isEmpty();
	@*/
	@Inject
	public TwoPhaseSet(final ObjectMapper mapper) {
		serializer = mapper;
		adds = new GSet<E>(mapper);
		removals = new GSet<E>(mapper);
	}

	public TwoPhaseSet(final ObjectMapper mapper, final byte[] value) {
		serializer = mapper;

		try {

			Map<String, JsonNode> retval = mapper.readValue(value, ref);

			adds = new GSet<E>(mapper, mapper.writeValueAsBytes(retval
					.get(ADD_TOKEN)));
			removals = new GSet<E>(mapper, mapper.writeValueAsBytes(retval
					.get(REMOVE_TOKEN)));

		} catch (IOException ioe) {
			throw new IllegalArgumentException("Invalid JSON.", ioe);
		}
	}

	private TwoPhaseSet(final ObjectMapper mapper, final GSet<E> adds,
			final GSet<E> removals) {
		serializer = mapper;
		this.adds = adds;
		this.removals = removals;
	}

	/*@
	@ ensures (\forall E val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
	@ ensures (\forall E val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
	@ ensures (\forall E val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
	@ ensures (\forall E val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
	@*/
	// changed from original: @Override
	public Void merge(final TwoPhaseSet<E> other) { // Change from the origin: Void <- TwoPhaseSet<E>
		GSet<E> a = new GSet<E>(serializer);
		GSet<E> r = new GSet<E>(serializer);

		a.addAll(adds);
		r.addAll(removals);

		a.addAll(other.adds);
		r.addAll(other.removals);
		// this merge function had TwoPhaseSet<E> output type.
		//return new TwoPhaseSet<E>(serializer, a, r);

		return null;
	}

	// Previously: ensures \result.equals(Sets.difference(adds, removals));
	/*@
	@ assignable \nothing;
	@ ensures (\forall E elem; adds.contains(elem) && removals.contains(elem) == false; \result.contains(elem));
	@ ensures (\forall E elem; \result.contains(elem); adds.contains(elem) && removals.contains(elem) == false);
	@*/
	// changed from original: @Override
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(Sets.difference(this.adds, this.removals));
	}

	// No need to annotate
	// changed from original: @Override
	public byte[] payload() {
		try {
			Map<String, JsonNode> retval = Maps.newHashMap();

			retval.put(ADD_TOKEN, serializer.readTree(adds.payload()));
			retval.put(REMOVE_TOKEN, serializer.readTree(removals.payload()));

			return serializer.writeValueAsBytes(retval);
		} catch (IOException ioe) {
			throw new IllegalStateException("Could not serialize.", ioe);
		}
	}

	/*@
	@ requires (removals.contains(obj) == false);
	@ assignable adds;
	@ ensures adds.contains(obj);
    @ ensures (\forall E elem; \old(adds.contains(elem)); adds.contains(elem));
    @ ensures (\forall E elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
    @ ensures \result == !(\old(adds.contains(obj)));
	@*/
	// changed from original: @Override
	public boolean add(final E obj) {
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
	// changed from original: @Override
	public boolean addAll(final Collection<? extends E> col) {
		Set<E> s = Sets.intersection(removals, Sets.newHashSet(col));

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
		removals.addAll(adds);

	}

	/*@
	@ assignable \nothing;
	@ ensures \result == !removals.contains(obj) && adds.contains(obj);
	@*/
	// changed from original: @Override
	public boolean contains(final Object obj) {
		return !removals.contains(obj) && adds.contains(obj);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; col.contains(elem); removals.contains(elem) == false) && (\forall E elem; col.contains(elem); adds.contains(elem));
	@*/
	// changed from original: @Override
	public boolean containsAll(final Collection<?> col) {
		Set<E> s = Sets.intersection(removals, Sets.newHashSet(col));
		return s.isEmpty() && adds.containsAll(col);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; adds.contains(elem); removals.contains(elem));
	@*/
	// changed from original: @Override
	public boolean isEmpty() {
		return removals.containsAll(adds);
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
	public boolean remove(final Object obj) {
		if (removals.contains(obj) || !adds.contains(obj)) {
			return false;
		}

		removals.add((E) obj);

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
	public boolean removeAll(final Collection<?> col) {
		checkNotNull(col);
		checkCollectionDoesNotContainNull(col);
		
		Set<E> input = Sets.newHashSet((Collection<E>) col);
		Set<E> intersection = Sets.intersection(this.adds, input);
		
		return this.removals.addAll(intersection);
	}

	// Omitted: requires col.contains(null) == false;
	/*@
	@ requires col.isEmpty() == false;
	@ assignable removals;
	@ ensures (\forall E elem; col.contains(elem) && adds.contains(elem) && \old(removals.contains(elem)) == false; !removals.contains(elem));
	@ ensures (\forall E elem; \old(removals.contains(elem)); removals.contains(elem));
	@ ensures (\forall E elem; removals.contains(elem) && \old(removals.contains(elem)) == false; adds.contains(elem) && col.contains(elem) == false);
	@ ensures \result == (\exists E elem; !col.contains(elem) && this.value().contains(elem); true);
	@*/
	// changed from original: @Override
	// changed from original: @SuppressWarnings("unchecked")
	public boolean retainAll(final Collection<?> col) {
		checkNotNull(col);
		checkCollectionDoesNotContainNull(col);

		Set<E> input = Sets.newHashSet((Collection<E>) col);
		Set<E> diff = Sets.difference(this.value(), input);

		return this.removeAll(diff);
	}

	// Previously: ensures \result == adds.value().size() - removals.value().size();
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public int size() {
		return this.adds.size() - this.removals.size();
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

	// Previously: \result == o.value().equals(this.value());
	// The problem was type casting, but we conclude we don't need any post conditions in equals method.
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public final boolean equals(@Nullable final Object o) {

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

	// Previously: ensures \result == this.value().hashCode();
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public int hashCode() {
		return this.value().hashCode();
	}

	// Previously: ensures \result.equals(this.value().toString());
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public String toString() {
		return this.value().toString();
	}
}
