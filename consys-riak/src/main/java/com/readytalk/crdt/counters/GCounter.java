package com.readytalk.crdt.counters;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
// this import is used by jml annotations so it's important to be.

import java.io.IOException;
import java.lang.reflect.Type;
import java.math.BigInteger;
import java.util.Map;

import javax.annotation.Nonnegative;
import javax.inject.Inject;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.base.Objects;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.readytalk.crdt.AbstractCRDT;
import com.readytalk.crdt.inject.ClientId;

import java.lang.String;




/**
 * Grow-only counter.  Does not support decrementing.
 *
 */
@ReplicatedModel public class GCounter extends AbstractCRDT<BigInteger, GCounter> implements CRDTCounter<BigInteger, GCounter> {
	// omitted in new versions: payload.containsKey(s) - payload.get(s) != null
	// Added to the origin code:
	//static final int numOfReplicas = 3;
	static final String[] keys = new String[] {"KeyA", "KeyB", "KeyC"};
	// End added part

	/*@
	@ public invariant this.value().compareTo(BigInteger.ZERO) != -1;
	@ public invariant (\forall String s; true ; this.payload.get(s).compareTo(BigInteger.ZERO) != -1);
	@*/

	// Change from the origin: We had this field:
	//private static final TypeReference<Map<String, BigInteger>> REF = new TypeReference<Map<String, BigInteger>>() {};

	private final String clientId;

	private final Map<String, BigInteger> payload = Maps.newHashMap();


	// Second idea: ensures (\forall BigInteger o : payload.values(); o.equals(BigInteger.ZERO));
	/*@
	@ ensures (\forall String s; true ; this.payload.get(s).equals(BigInteger.ZERO));
	@ ensures this.clientId.equals(client);
	@*/
	@Inject
	public GCounter(final ObjectMapper mapper, @ClientId final String client) {
		super(mapper);

		clientId = client;
		
		payload.put(clientId, BigInteger.ZERO);
	}

	// Another constructor
	/* Change from the origin: We had this constructor:
	//@SuppressWarnings("unchecked")
	public GCounter(final ObjectMapper mapper, @ClientId final String client, final byte[] value) {
		this(mapper, client);

		

		try {
			this.payload.putAll((Map<String, BigInteger>) serializer().readValue(value, REF));
		} catch (IOException ioe) {
			throw new IllegalArgumentException("Unable to deserialize payload.", ioe);
		}
	}
	End change from the origin */

	// Another constructor
	/*private GCounter(final ObjectMapper mapper, @ClientId final String client, final Map<String, BigInteger> value) {
		this(mapper, client);

		this.payload.putAll(value);
	}*/

	/*@
	@ ensures (\forall String s; true ;
				other.payload.get(s).compareTo(\old(payload.get(s))) == 1 ? this.payload.get(s).equals(other.payload.get(s)) : this.payload.get(s).equals(\old(payload.get(s))) );
	@ ensures clientId.equals(\old(clientId));
	@*/
	// changed from original: @Override
	public void merge(final GCounter other) { // Change from the origin: void <- GCounter
		Map<String, BigInteger> retmap = Maps
				.newHashMapWithExpectedSize(Math.max(payload.size(), other.payload.size()));
		retmap.putAll(payload);

		for (Map.Entry<String, BigInteger> o : other.payload.entrySet()) {
			BigInteger value = Objects.firstNonNull(retmap.get(o.getKey()), BigInteger.ZERO);

			retmap.put(o.getKey(), o.getValue().max(value));
		}
		// this merge function had GCounter output type.
		//return new GCounter(serializer(), clientId, retmap);
	}

	// Prevously: ensures \result.intValue() == (\sum int i; i >= 0 && i < this.payload.values().toArray().length; this.payload.values().toArray(new BigInteger[0])[i].intValue());
	/*@
	@ assignable \nothing;
	@ ensures \result.intValue() == (\sum int i; i >= 0 && i < numOfReplicas(); payload.get(keys[i]).intValue());
	@*/
	// Changed from the original: @Override
	public BigInteger value() {
		BigInteger retval = BigInteger.ZERO;

		for (BigInteger o : payload.values()) {
			retval = retval.add(o);
		}

		return retval;
	}

	/*@
	@ assignable this.payload.get(clientId);
	@ ensures this.payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(1))));
	@ ensures \result.equals(this.value());
	@*/
	public BigInteger increment() {
		return this.increment(1);
	}

	/*@
	@ requires n >= 0;
	@ assignable this.payload.get(clientId);
	@ ensures this.payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(n))));
	@ ensures \result.equals(this.value());
	@*/
	// Changed from the original: @Override
	public BigInteger increment(@Nonnegative final int n) {
		Preconditions.checkArgument(n >= 0);
		
		BigInteger retval = payload.get(clientId).add(BigInteger.valueOf(n));

		payload.put(clientId, retval);

		return this.value();
	}

	// no need to annotate
	// Changed from the original: @Override
	public byte[] payload() {
		try {
			return serializer().writeValueAsBytes(payload);
		} catch (IOException ioe) {
			throw new IllegalStateException("Cannot serialize payload.");
		}
	}

	//@ requires false;
	// Changed from the original: @Override
	public BigInteger decrement() {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	// Changed from the original: @Override
	public BigInteger decrement(@Nonnegative final int n) {
		throw new UnsupportedOperationException();
	}

	// Prevously: \result == (this.value().intValue() == o.value().intValue());
	// The problem was type casting but we conclude we don't need any post conditions in equals method.
	/*@
	@ assignable \nothing;
	@
	@*/
	// Changed from the original: @Override
	public boolean equals(final Object o) {
		if (!(o instanceof GCounter)) {
			return false;
		}

		GCounter t = (GCounter) o;

		if (this == t) {
			return true;
		} else {
			return this.value().equals(t.value());
		}
	}
	// ensures \result == this.value().hashCode();
	/*@
	@ assignable \nothing;
	@ ensures \result == this.value().hashCode();
	@*/
	// Changed from the original: @Override
	public int hashCode() {
		return this.value().hashCode();
	}

}
