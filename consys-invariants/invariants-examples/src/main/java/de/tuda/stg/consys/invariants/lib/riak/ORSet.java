package de.tuda.stg.consys.invariants.lib.riak;



import com.google.common.base.Predicate;
import com.google.common.collect.*;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.io.IOException;
import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;

@ReplicatedModel public class ORSet<E> {

	private static final String ELEMENTS_TOKEN = "e";
	private static final String TOMBSTONES_TOKEN = "t";

	private final Multimap<E, UUID> elements = LinkedHashMultimap.create();
	private final Multimap<E, UUID> tombstones = LinkedHashMultimap.create();



	/*@
	@ ensures elements.isEmpty();
	@ ensures tombstones.isEmpty();
	@*/
	public ORSet() {

	}



	//@ assignable elements;
	//@ ensures elements.containsKey(value);
	//@ ensures (\exists UUID u; \old(elements.containsValue(u)) == false; elements.containsValue(u));
	//@ ensures (\forall UUID u; \old(elements.containsValue(u)) == false && elements.containsValue(u); (\forall UUID u2; \old(elements.containsValue(u2)) == false && elements.containsValue(u2); u2.equals(u)) );
	//@ ensures (\forall UUID u; \old(elements.containsValue(u)); elements.containsValue(u));
	//@ ensures (\forall E elem; elem.equals(value) == false; elements.get(elem).equals(\old(elements.get(elem))));
	//@ ensures \result == !(\old(elements.containsKey(value)));
	public boolean add(final E value) {
		checkNotNull(value);
		
		UUID uuid = UUID.randomUUID();
		boolean retval = !elements.containsKey(value);

		elements.put(value, uuid);

		return retval;
	}

	/*@
	@ assignable elements;
	@ ensures (\forall E elem; values.contains(elem); elements.containsKey(elem));
	@ ensures (\forall E elem; values.contains(elem); (\exists UUID u; \old(elements.get(elem)).contains(u) == false; elements.get(elem).contains(u)) );
	@ ensures (\forall E elem; values.contains(elem); (\forall UUID u; \old(elements.get(elem)).contains(u) == false && elements.get(elem).contains(u);
														(\forall UUID u2; \old(elements.get(elem)).contains(u2) == false && elements.get(elem).contains(u2); u2.equals(u) ) ) );
	@ ensures (\forall UUID u; \old(elements.containsValue(u)); elements.containsValue(u));
	@ ensures (\forall E elem; values.contains(elem) == false; elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures \result == (\exists E elem; values.contains(elem); \old(elements.containsKey(elem)) == false);
	@*/
	public boolean addAll(final Collection<? extends E> values) {
		checkNotNull(values);
//		checkCollectionDoesNotContainNull(values);

		boolean retval = false;

		for (E o : values) {
			retval |= this.add(o);
		}

		return retval;
	}

	/*@
	@ assignable elements, tombstones;
	@ ensures elements.isEmpty();
	@ ensures (\forall UUID u; \old(elements.containsValue(u)); tombstones.containsValue(u));
	@ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
	@ ensures (\forall UUID u; tombstones.containsValue(u); \old(elements.containsValue(u)) || \old(tombstones.containsValue(u)) );
	@*/
	public void clear() {
		this.tombstones.putAll(this.elements);
		this.elements.clear();

	}

	/*@
	@ assignable \nothing;
	@ ensures \result == elements.containsKey(value);
	@*/
	public boolean contains(final Object value) {
		checkNotNull(value);
		
		return this.elements.containsKey(value);
	}

	/*@
	@ assignable \nothing;
	@ ensures \result == (\forall E elem; values.contains(elem); this.value().contains(elem));
	@*/
	public boolean containsAll(final Collection<?> values) {
//		checkCollectionDoesNotContainNull(values);
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

	//@ requires false;
	public Iterator<E> iterator() {
		return Iterators
				.unmodifiableIterator(this.elements.keySet().iterator());
	}


	/*@
	@ assignable elements, tombstones;
	@ ensures elements.containsKey(value) == false;
	@ ensures (\forall E elem; elem.equals(value) == false; elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures (\forall UUID u; \old(elements.get(value)).contains(u); tombstones.containsValue(u));
	@ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
	@ ensures (\forall UUID u; tombstones.containsValue(u); \old(elements.get(value)).contains(u) || \old(tombstones.containsValue(u)) );
	@ ensures \result == \old(elements.containsValue(value));
	@*/
	@SuppressWarnings("unchecked")
	public boolean remove(final Object value) {
		checkNotNull(value);

		this.tombstones.putAll((E) value, elements.get((E) value));

		return elements.removeAll(value).size() > 0;

	}

	/*@
	@ assignable elements, tombstones;
	@ ensures (\forall E elem; values.contains(elem); elements.containsKey(elem) == false);
	@ ensures (\forall E elem; values.contains(elem) == false; elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures (\forall E elem; values.contains(elem); (\forall UUID u; \old(elements.get(elem)).contains(u); tombstones.containsValue(u)) );
	@ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
	@ ensures (\forall UUID u; tombstones.containsValue(u); (\exists E elem; values.contains(elem); \old(elements.get(elem)).contains(u)) || \old(tombstones.containsValue(u)) );
	@ ensures \result == (\exists E elem; values.contains(elem) && \old(elements.containsKey(elem)); true);
	@*/
	public boolean removeAll(final Collection<?> values) {
		checkNotNull(values);
//		checkCollectionDoesNotContainNull(values);

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
	@ ensures (\forall E elem; values.contains(elem); elements.get(elem).equals(\old(elements.get(elem))));
	@ ensures (\forall E elem; values.contains(elem) == false; elements.containsKey(elem) == false);
	@ ensures (\forall E elem; values.contains(elem) == false; (\forall UUID u; \old(elements.get(elem)).contains(u); tombstones.containsValue(u)) );
	@ ensures (\forall UUID u; \old(tombstones.containsValue(u)); tombstones.containsValue(u));
	@ ensures (\forall UUID u; tombstones.containsValue(u); (\exists E elem; values.contains(elem) == false; \old(elements.get(elem)).contains(u)) || \old(tombstones.containsValue(u)) );
	@ ensures \result == (\exists E elem; values.contains(elem) == false && \old(elements.containsKey(elem)); true);
	@*/
	@SuppressWarnings("unchecked")
	public boolean retainAll(final Collection<?> values) {
		checkNotNull(values);
//		checkCollectionDoesNotContainNull(values);
		
		Set<E> input = Sets.newHashSet((Collection<E>)values);
		Set<E> diff = Sets.difference(this.elements.keySet(), input);
		
		return this.removeAll(diff);
	}

	//@ requires false;
	//@ assignable \nothing;
	public int size() {
		return elements.keySet().size();
	}

	// Previously: ensures \result.equals(elements.keySet().toArray());
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public Object[] toArray() {
		return elements.keySet().toArray();
	}

	// Previously: ensures \result.equals(elements.keySet().toArray(arg));
	/*@
	@ assignable \nothing;
	@*/
	// changed from original: @Override
	public <T> T[] toArray(final T[] arg) {
		return elements.keySet().toArray(arg);
	}

	/*@
	@ ensures (\forall UUID u; (\old(this.elements.containsValue(u)) || other.elements.containsValue(u)) && \old(this.tombstones.containsValue(u)) == false && other.tombstones.containsValue(u) == false ; elements.containsValue(u) );
	@ ensures (\forall UUID u; elements.containsValue(u); (\old(this.elements.containsValue(u)) || other.elements.containsValue(u)) && \old(this.tombstones.containsValue(u)) == false && other.tombstones.containsValue(u) == false );
	@ ensures (\forall UUID u; \old(this.tombstones.containsValue(u)) || other.tombstones.containsValue(u); tombstones.containsValue(u));
	@ ensures (\forall UUID u; tombstones.containsValue(u); \old(this.tombstones.containsValue(u)) || other.tombstones.containsValue(u));
	@*/
	public Void merge(final ORSet<E> other) { // Change from the origin: Void <- ORSet<E>
		// Changed from the origin. Because origin return a new merged object but we don't.
		this.elements.putAll(other.elements);
		this.tombstones.putAll(other.tombstones);
		this.elements.removeAll(this.tombstones);
		return null;
		// Origin version:
//		ORSet<E> retval = new ORSet<E>(serializer());
//		retval.elements.putAll(this.elements);
//		retval.elements.putAll(other.elements);
//		retval.tombstones.putAll(this.tombstones);
//		retval.tombstones.putAll(other.tombstones); // Changed from the origin: retval.tombstones.putAll(other.elements); because we think that was a bug from riak library developers.
//		retval.elements.removeAll(retval.tombstones);
		// this merge function had ORSet<E> output type.
		//return retval;
	}

	/*@
	@ assignable \nothing;
	@ ensures (\forall E elem; \result.contains(elem); elements.containsKey(elem));
	@ ensures (\forall E elem; elements.containsKey(elem); \result.contains(elem));
	@*/
	public ImmutableSet<E> value() {
		return ImmutableSet.copyOf(elements.keySet());
	}

	//@ requires false;
	public byte[] payload() {
//		Map<String, Object> retval = Maps.newLinkedHashMap();
//
//		retval.put(ELEMENTS_TOKEN, elements.asMap());
//		retval.put(TOMBSTONES_TOKEN, tombstones.asMap());
//
//		try {
//			return serializer().writeValueAsBytes(retval);
//		} catch (IOException ex) {
//			throw new IllegalStateException("Unable to serialize object.", ex);
//		}
		return null;
	}



	//@ requires false;
	//@ assignable \nothing;
	public final boolean equals(final Object o) {
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
	@*/
	public final int hashCode() {
		return this.value().hashCode();
	}

	/*@
	@ assignable \nothing;
	@*/
	public String toString() {
		return this.value().toString();
	}
}
