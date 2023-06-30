package de.tuda.stg.consys.invariants.lib.riak;


import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.tuda.stg.consys.annotations.invariants.SetUtils;

import static com.google.common.base.Preconditions.checkNotNull;


/**
 * Grow-only Sets. Do not implement the remove operations.
 * 
 */

@ReplicatedModel public class GSet<E> {

	private final Set<E> delegate = Sets.newLinkedHashSet();

	//@ ensures this.delegate.isEmpty();
	public GSet() {
	}

	//@ assignable \nothing;
	//@ ensures \result.equals(delegate);
	protected Set<E> delegate() {
		return delegate;
	}

	//@ requires false;
	public void clear() {
		throw new UnsupportedOperationException();

	}

	//@ requires false;
	public Iterator<E> iterator() {
		return Iterators.unmodifiableIterator(/*Inlined call from super class.*/delegate.iterator());
	}

	//@ requires false;
	public boolean remove(final Object o) {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	public boolean removeAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	public boolean retainAll(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	//@ ensures (\forall E val; \old(delegate.contains(val)) || other.delegate.contains(val); delegate.contains(val));
	//@ ensures (\forall E val; delegate.contains(val); \old(delegate.contains(val)) || other.delegate.contains(val));
	public Void merge(final GSet<E> other) {
		Set<E> retval = Sets.newLinkedHashSet();

		retval.addAll(delegate);
		retval.addAll(other.delegate);

		delegate.addAll(retval);
		return null;
	}

	//@ assignable \nothing;
	//@ ensures \result.equals(delegate);
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(delegate);
	}


	//@ requires false;
	public byte[] payload() {
//		try {
//			return serializer.writeValueAsBytes(delegate);
//		} catch (IOException ioe) {
//			throw new IllegalStateException("Unable to serialize.", ioe);
//		}
		return null;
	}

	//@ assignable \nothing;
	//@ ensures \result == delegate.contains(object);
	public boolean contains(final Object object) {
		checkNotNull(object);

		return delegate.contains(object);
	}

	//@ assignable delegate;
	//@ ensures delegate.contains(element);
	//@ ensures (\forall E elem; \old(delegate.contains(elem)); delegate.contains(elem));
    //@ ensures (\forall E elem; delegate.contains(elem) && elem.equals(element) == false; \old(delegate.contains(elem)));
    //@ ensures \result == !(\old(delegate.contains(element)));
	public boolean add(final E element) {
		checkNotNull(element);
		return delegate.add(element);
	}

	//@ assignable \nothing;
	//@ ensures \result == (\forall E elem; collection.contains(elem); delegate.contains(elem));
	public boolean containsAll(final Collection<?> collection) {
//		checkCollectionDoesNotContainNull(collection);

		return delegate.containsAll(collection);
	}

	//@ assignable delegate;
	//@ ensures (\forall E elem; collection.contains(elem); delegate.contains(elem));
	//@ ensures (\forall E elem; \old(delegate.contains(elem)); delegate.contains(elem));
	//@ ensures (\forall E elem; delegate.contains(elem) && collection.contains(elem) == false; \old(delegate.contains(elem)));
	//@ ensures \result == !(\forall E elem; collection.contains(elem); \old(delegate.contains(elem)));
	//@ ensures delegate == SetUtils.union(delegate, collection);
	public boolean addAll(final Collection<? extends E> collection) {
//		checkCollectionDoesNotContainNull(collection);
		return delegate.addAll(collection);
	}

}
