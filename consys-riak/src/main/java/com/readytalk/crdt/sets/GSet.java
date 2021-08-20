package com.readytalk.crdt.sets;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.readytalk.crdt.util.CollectionUtils.checkCollectionDoesNotContainNull;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import javax.inject.Inject;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.collect.ForwardingSet;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.Sets;

/**
 * Grow-only Sets. Do not implement the remove operations.
 * 
 */

@ReplicatedModel public class GSet<E> extends ForwardingSet<E> implements
		CRDTSet<E, ImmutableSet<E>, GSet<E>> {

	private final Set<E> delegate = Sets.newLinkedHashSet();

	private final ObjectMapper serializer;

	private final TypeReference<List<E>> ref = new TypeReference<List<E>>() {

	};

	//@ ensures this.delegate.isEmpty();
	@Inject
	public GSet(final ObjectMapper mapper) {
		serializer = mapper;
	}

	@SuppressWarnings("unchecked")
	public GSet(final ObjectMapper mapper, final byte[] payload) {
		serializer = mapper;

		try {
			delegate.addAll((List<E>) serializer.readValue(payload, ref));
		} catch (IOException ioe) {
			throw new IllegalArgumentException("Unable to deserialize.", ioe);
		}

	}

	private GSet(final ObjectMapper mapper, final Set<E> set) {
		serializer = mapper;

		delegate.addAll(set);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result.equals(delegate);
	@*/
	// changed from original: @Override
	protected Set<E> delegate() {
		return delegate;
	}

	//@ requires false;
	// changed from original: @Override
	public void clear() {
		throw new UnsupportedOperationException();

	}


	// No annotations I think...
	// changed from original: @Override
	public Iterator<E> iterator() {
		return Iterators.unmodifiableIterator(super.iterator());
	}

	//@ requires false;
	// changed from original: @Override
	public boolean remove(final Object o) {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	// changed from original: @Override
	public boolean removeAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	// changed from original: @Override
	public boolean retainAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	/*@
	@ ensures (\forall E val; \old(delegate.contains(val)) || other.delegate.contains(val); delegate.contains(val));
	@ ensures (\forall E val; delegate.contains(val); \old(delegate.contains(val)) || other.delegate.contains(val));
	@*/
	// changed from original: @Override
	public Void merge(final GSet<E> other) { // Change from the origin: Void <- GSet<E>
		Set<E> retval = Sets.newLinkedHashSet();

		retval.addAll(delegate);
		retval.addAll(other.delegate);

		// this merge function had GSet<E> output type.
		//return new GSet<E>(serializer, retval);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result.equals(ImmutableSet.copyOf(delegate));
	@*/
	// changed from original: @Override
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(delegate);
	}

	// No annotations needed
	// changed from original: @Override
	public byte[] payload() {
		try {
			return serializer.writeValueAsBytes(delegate);
		} catch (IOException ioe) {
			throw new IllegalStateException("Unable to serialize.", ioe);
		}
	}

	// How about using super in the annotations?
	/*@
	@ assignable \nothing;
	@ ensures \result == delegate.contains(object);
	@*/
	// changed from original: @Override
	public boolean contains(final Object object) {
		checkNotNull(object);

		return super.contains(object);
	}

	/*@
	@ assignable delegate;
	@ ensures delegate.contains(element);
	@ ensures (\forall E elem; \old(delegate.contains(elem)); delegate.contains(elem));
    @ ensures (\forall E elem; delegate.contains(elem) && elem.equals(element) == false; \old(delegate.contains(elem)));
    @ ensures \result == !(\old(delegate.contains(element)));
	@*/
	// changed from original: @Override
	public boolean add(final E element) {
		checkNotNull(element);

		return super.add(element);
	}
	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; collection.contains(elem); delegate.contains(elem));
	@*/
	// changed from original: @Override
	public boolean containsAll(final Collection<?> collection) {
		checkCollectionDoesNotContainNull(collection);

		return super.containsAll(collection);
	}

	/*@
	@ assignable delegate;
	@ ensures (\forall E elem; collection.contains(elem); delegate.contains(elem));
	@ ensures (\forall E elem; \old(delegate.contains(elem)); delegate.contains(elem));
	@ ensures (\forall E elem; delegate.contains(elem) && collection.contains(elem) == false; \old(delegate.contains(elem)));
	@ ensures \result == !(\forall E elem; collection.contains(elem); \old(delegate.contains(elem)));
	@*/
	// changed from original: @Override
	public boolean addAll(final Collection<? extends E> collection) {
		checkCollectionDoesNotContainNull(collection);

		return super.addAll(collection);
	}

}
