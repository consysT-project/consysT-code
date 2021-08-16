package com.readytalk.crdt.sets;


import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.readytalk.crdt.util.CollectionUtils.checkCollectionDoesNotContainNull;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import javax.annotation.Nullable;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;
import com.readytalk.crdt.AbstractCRDT;

@ReplicatedModel public class ORSet<E> extends AbstractCRDT<ImmutableSet<E>, ORSet<E>> implements
		CRDTSet<E, ImmutableSet<E>, ORSet<E>> {

	private static final String ELEMENTS_TOKEN = "e";
	private static final String TOMBSTONES_TOKEN = "t";

	private final Multimap<E, UUID> elements = LinkedHashMultimap.create();
	private final Multimap<E, UUID> tombstones = LinkedHashMultimap.create();



	/*@
	@ ensures elements.isEmpty();
	@ ensures tombstones.isEmpty();
	@*/
	public ORSet(final ObjectMapper mapper) {
		super(mapper);
	}

	// Another constructor
	public ORSet(final ObjectMapper mapper, final byte[] value) {
		super(mapper);

		TypeReference<Map<String, Map<E, Collection<UUID>>>> ref =
				new TypeReference<Map<String, Map<E, Collection<UUID>>>>() {

		};

		try {
			Map<String, Map<E, Collection<UUID>>> s1 = mapper.readValue(value,
					ref);

			Map<E, Collection<UUID>> e = s1.get(ELEMENTS_TOKEN);
			Map<E, Collection<UUID>> t = s1.get(TOMBSTONES_TOKEN);

			for (Map.Entry<E, Collection<UUID>> o : e.entrySet()) {
				elements.putAll(o.getKey(), o.getValue());
			}

			for (Map.Entry<E, Collection<UUID>> o : t.entrySet()) {
				tombstones.putAll(o.getKey(), o.getValue());
			}

		} catch (IOException ex) {
			throw new IllegalArgumentException("Unable to deserialize.", ex);
		}

	}


	/*@
	@ assignable elements;
	@ ensures elements.containsKey(value);
	@ ensures elements.get(value).size() == (\old(elements.get(value))).size() + 1;
	@ ensures (\forall E elem; elem.equals(value) == false && \old(elements.containsKey(elem)); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures \result == !(\old(elements.containsKey(value)));
	@*/
	// changed from original: @Override
	public boolean add(final E value) {
		checkNotNull(value);
		
		UUID uuid = UUID.randomUUID();
		boolean retval = !elements.containsKey(value);

		elements.put(value, uuid);

		return retval;
	}

	/*@
	@ assignable elements;
	@ ensures (\forall E elem; values.contains(elem); elements.get(elem).size() == (\old(elements.get(elem))).size() + 1);
	@ ensures (\forall E elem; values.contains(elem) == false && \old(elements.containsKey(elem)); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures \result == (\exists E elem; values.contains(elem); \old(elements.containsKey(elem)) == false);
	@*/
	// changed from original: @Override
	public boolean addAll(final Collection<? extends E> values) {
		checkNotNull(values);
		checkCollectionDoesNotContainNull(values);

		boolean retval = false;

		for (E o : values) {
			retval |= this.add(o);
		}

		return retval;
	}

	/*@
	@ assignable elements, tombstones;
	@ ensures elements.isEmpty();
	@ ensures (\forall E elem; \old(elements.containsKey(elem)); tombstones.get(elem).containsAll(\old(elements.get(elem))));
	@ ensures (\forall E elem; \old(tombstones.containsKey(elem)); tombstones.get(elem).containsAll(\old(tombstones.get(elem))));
	@*/
	// changed from original: @Override
	public void clear() {
		this.tombstones.putAll(this.elements);
		this.elements.clear();

	}

	/*@
	@ assignable \nothing;
	@ ensures \result == elements.containsKey(value);
	@*/
	// changed from original: @Override
	public boolean contains(final Object value) {
		checkNotNull(value);
		
		return this.elements.containsKey(value);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == this.value().containsAll(values);
	@*/
	// changed from original: @Override
	public boolean containsAll(final Collection<?> values) {
		checkCollectionDoesNotContainNull(values);
		return this.value().containsAll(values);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == elements.isEmpty();
	@*/
	// changed from original: @Override
	public boolean isEmpty() {
		return elements.isEmpty();
	}

	// No need to annotate.
	// changed from original: @Override
	public Iterator<E> iterator() {
		return Iterators
				.unmodifiableIterator(this.elements.keySet().iterator());
	}


	/*@
	@ assignable elements, tombstones;
	@ ensures elements.containsKey(value) == false;
	@ ensures (\forall E elem; elem.equals(value) == false && \old(elements.containsKey(elem)); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures tombstones.get(value).containsAll(\old(elements.get(value)));
	@ ensures (\forall E elem; \old(tombstones.containsKey(elem)); tombstones.get(elem).containsAll(\old(tombstones.get(elem))));
	@ ensures \result == (\old(elements.get(value)).isEmpty() == false);
	@*/
	@SuppressWarnings("unchecked")
	// changed from original: @Override
	public boolean remove(final Object value) {
		checkNotNull(value);

		this.tombstones.putAll((E) value, elements.get((E) value));

		return elements.removeAll(value).size() > 0;

	}

	/*@
	@ assignable elements, tombstones;
	@ ensures (\forall E elem; values.contains(elem); elements.containsKey(elem) == false);
	@ ensures (\forall E elem; values.contains(elem) == false && \old(elements.containsKey(elem)); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures (\forall E elem; values.contains(elem); tombstones.get(elem).containsAll(\old(elements.get(elem))));
	@ ensures (\forall E elem; \old(tombstones.containsKey(elem)); tombstones.get(elem).containsAll(\old(tombstones.get(elem))));
	@ ensures \result == (\exists E elem; values.contains(elem); (\old(elements.get(elem)).isEmpty() == false));
	@*/
	// changed from original: @Override
	public boolean removeAll(final Collection<?> values) {
		checkNotNull(values);
		checkCollectionDoesNotContainNull(values);

		Multimap<E, UUID> subset = Multimaps.filterKeys(elements,
				new Predicate<E>() {

					@Override
					public boolean apply(final E input) {

						return values.contains(input);
					}
				});

		if (subset.isEmpty()) {
			return false;
		}

		for (E o : Sets.newLinkedHashSet(subset.keySet())) {
			Collection<UUID> result = this.elements.removeAll(o);

			this.tombstones.putAll(o, result);
		}

		return true;
	}

	/*@
	@ assignable elements, tombstones;
	@ ensures (\forall E elem; values.contains(elem) && \old(elements.containsKey(elem)); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures (\forall E elem; values.contains(elem) == false; elements.containsKey(elem) == false);
	@ ensures (\forall E elem; values.contains(elem) == false; tombstones.get(elem).containsAll(\old(elements.get(elem))));
	@ ensures (\forall E elem; \old(tombstones.containsKey(elem)); tombstones.get(elem).containsAll(\old(tombstones.get(elem))));
	@ ensures \result == (\exists E elem; values.contains(elem) == false && this.value().contains(elem); true);
	@*/
	// changed from original: @Override
	@SuppressWarnings("unchecked")
	public boolean retainAll(final Collection<?> values) {
		checkNotNull(values);
		checkCollectionDoesNotContainNull(values);
		
		Set<E> input = Sets.newHashSet((Collection<E>)values);
		Set<E> diff = Sets.difference(this.elements.keySet(), input);
		
		return this.removeAll(diff);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == elements.keySet().size();
	@*/
	// changed from original: @Override
	public int size() {
		return elements.keySet().size();
	}

	/*@
	@ assignable \nothing;
	@ ensures \result.equals(elements.keySet().toArray());
	@*/
	// changed from original: @Override
	public Object[] toArray() {
		return elements.keySet().toArray();
	}

	/*@
	@ assignable \nothing;
	@ ensures \result.equals(elements.keySet().toArray(arg));
	@*/
	// changed from original: @Override
	public <T> T[] toArray(final T[] arg) {
		return elements.keySet().toArray(arg);
	}

	/*@
	@ ensures (\forall E elem; \old(elements.containsKey(elem)) && tombstones.containsKey(elem) == false; elements.containsAll(\old(elements.get(elem))));
	@ ensures (\forall E elem; other.elements.containsKey(elem) && tombstones.containsKey(elem) == false; elements.containsAll(other.element.get(elem)));
	@ ensures (\forall E elem; tombstones.containsKey(elem); elements.containsKey(elem) == false);
	@ ensures (\forall E elem; elements.containsKey(elem); tombstones.containsKey(elem) == false);
	@ ensures (\forall E elem; elements.containsKey(elem); other.elements.get(elem).addAll(\old(elements.get(elem))).containsAll(elements.get(elem)));
	@ ensures (\forall E elem; \old(tombstones.containsKey(elem)); tombstones.containsAll(\old(tombstones.get(elem))));
	@ ensures (\forall E elem; other.tombstones.containsKey(elem); tombstones.containsAll(other.tombstones.get(elem)));
	@ ensures (\forall E elem; tombstones.containsKey(elem); other.tombstones.get(elem).addAll(\old(tombstones.get(elem))).containsAll(tombstones.get(elem)));
	@*/
	// changed from original: @Override
	public ORSet<E> merge(final ORSet<E> other) {
		ORSet<E> retval = new ORSet<E>(serializer());

		retval.elements.putAll(this.elements);
		retval.elements.putAll(other.elements);
		retval.tombstones.putAll(this.tombstones);
		retval.tombstones.putAll(other.elements);

		retval.elements.removeAll(retval.tombstones);

		return retval;
	}

	/*@
	@ assignable \nothing;
	@ ensures (\forall E elem; \result.contains(elem); elements.containsKey(elem));
	@ ensures (\forall E elem; elements.containsKey(elem); \result.contains(elem));
	@*/
	// changed from original: @Override
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(elements.keySet());
	}

	// No need to annotate.
	// changed from original: @Override
	public byte[] payload() {
		Map<String, Object> retval = Maps.newLinkedHashMap();

		retval.put(ELEMENTS_TOKEN, elements.asMap());
		retval.put(TOMBSTONES_TOKEN, tombstones.asMap());

		try {
			return serializer().writeValueAsBytes(retval);
		} catch (IOException ex) {
			throw new IllegalStateException("Unable to serialize object.", ex);
		}
	}

	// The problem was type casting but we conclude we don't need any post conditions in equals method.
	// We decided there is no need to annotate equals().
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public final boolean equals(@Nullable final Object o) {
		if (!(o instanceof ORSet)) {
			return false;
		}

		ORSet<?> t = (ORSet<?>) o;

		if (this == t) {
			return true;
		} else {
			return this.value().equals(t.value());
		}
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == this.value().hashCode();
	@*/
	// changed from original: @Override
	public final int hashCode() {
		return this.value().hashCode();
	}

	/*@
	@ assignable \nothing;
	@ ensures \result.equals(this.value().toString());
	@*/
	// changed from original: @Override
	public String toString() {
		return this.value().toString();
	}
}
