package com.readytalk.crdt.counters;

import java.io.IOException;
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

/**
 * Grow-only counter.  Does not support decrementing.
 *
 */
public class GCounter extends AbstractCRDT<BigInteger, GCounter> implements CRDTCounter<BigInteger, GCounter> {

	/*@
	@ public invariant value().compareTo(BigInteger.ZERO) != -1;
	@ public invariant (\forall String s; payload.get(s) != null; payload.get(s).compareTo(BigInteger.ZERO) != -1);
	@*/

	private static final TypeReference<Map<String, BigInteger>> REF = new TypeReference<Map<String, BigInteger>>() {

	};
	
	private final String clientId;

	private final Map<String, BigInteger> payload = Maps.newHashMap();


	// Second idea: ensures (\forall BigInteger o : payload.values(); o.equals(BigInteger.ZERO));
	/*@
	@ ensures (\forall String s; payload.get(s) != null; payload.get(s).equals(BigInteger.ZERO));
	@ ensures clientId.equals(client);
	@*/
	@Inject
	public GCounter(final ObjectMapper mapper, @ClientId final String client) {
		super(mapper);

		clientId = client;
		
		payload.put(clientId, BigInteger.ZERO);
	}

	// Another constructor
	@SuppressWarnings("unchecked")
	public GCounter(final ObjectMapper mapper, @ClientId final String client, final byte[] value) {
		this(mapper, client);

		

		try {
			this.payload.putAll((Map<String, BigInteger>) serializer().readValue(value, REF));
		} catch (IOException ioe) {
			throw new IllegalArgumentException("Unable to deserialize payload.", ioe);
		}
	}

	// Another constructor
	private GCounter(final ObjectMapper mapper, @ClientId final String client, final Map<String, BigInteger> value) {
		this(mapper, client);

		this.payload.putAll(value);
	}

	/*@
	@ ensures (\forall String s; \old(payload.get(s)) != null;
				other.payload.get(s).compareTo(\old(payload.get(s))) == 1 ? payload.get(s).equals(other.payload.get(s)) : payload.get(s).equals(\old(payload.get(s))) );
	@ ensures clientId.equals(\old(clientId));
	@*/
	@Override
	public GCounter merge(final GCounter other) {
		Map<String, BigInteger> retmap = Maps
				.newHashMapWithExpectedSize(Math.max(payload.size(), other.payload.size()));
		retmap.putAll(payload);

		for (Map.Entry<String, BigInteger> o : other.payload.entrySet()) {
			BigInteger value = Objects.firstNonNull(retmap.get(o.getKey()), BigInteger.ZERO);

			retmap.put(o.getKey(), o.getValue().max(value));
		}

		return new GCounter(serializer(), clientId, retmap);
	}

	// Not correct one. There might be no support for \sum BigInteger.
	/*@
	@ assignable \nothing;
	@ ensures \result == (\sum BigInteger o : payload.values(); o);
	@*/
	@Override
	public BigInteger value() {
		BigInteger retval = BigInteger.ZERO;

		for (BigInteger o : payload.values()) {
			retval = retval.add(o);
		}

		return retval;
	}

	/*@
	@ assignable payload.get(clientId);
	@ ensures payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(1))));
	@*/
	public BigInteger increment() {
		return this.increment(1);
	}

	/*@
	@ requires n >= 0;
	@ assignable payload.get(clientId);
	@ ensures payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(n))));
	@*/
	@Override
	public BigInteger increment(@Nonnegative final int n) {
		Preconditions.checkArgument(n >= 0);
		
		BigInteger retval = payload.get(clientId).add(BigInteger.valueOf(n));

		payload.put(clientId, retval);

		return this.value();
	}

	// no need to annotate
	@Override
	public byte[] payload() {
		try {
			return serializer().writeValueAsBytes(payload);
		} catch (IOException ioe) {
			throw new IllegalStateException("Cannot serialize payload.");
		}
	}

	// @ requires false;
	@Override
	public BigInteger decrement() {
		throw new UnsupportedOperationException();
	}

	// @ requires false;
	@Override
	public BigInteger decrement(@Nonnegative final int n) {
		throw new UnsupportedOperationException();
	}

	// Should we have annotations for equals method? - should we care about Object o?
	/*@
	@ assignable nothing;
	@ ensures \result == o.value().equals(value());
	@*/
	@Override
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

	/*@
	@ assignable \nothing;
	@ ensures \result == value().hashCode();
	@*/
	@Override
	public int hashCode() {
		return this.value().hashCode();
	}

}
