package de.tuda.stg.consys.invariants.lib.riak;

import com.google.common.base.Objects;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.math.BigInteger;
import java.util.Map;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;


/**
 * Grow-only counter.  Does not support decrementing.
 *
 */
@ReplicatedModel public class GCounter {

// private static final TypeReference<Map<String, BigInteger>> REF = new TypeReference<Map<String, BigInteger>>() {};

	public static final String[] KEYS = new String[] {"dummy-00", "dummy-01", "dummy-02", "dummy-03", "dummy-04", "dummy-05", "dummy-06", "dummy-07"};

	private final String clientId;
	private final Map<String, BigInteger> payload = Maps.newHashMap();


	/*@
	@ ensures (\forall String s; true ; this.payload.get(s).equals(BigInteger.ZERO));
	@ ensures this.clientId.equals(client);
	@*/
	public GCounter(final String client) {
		clientId = client;
		payload.put(clientId, BigInteger.ZERO);
	}

//	//@SuppressWarnings("unchecked")
//	public GCounter(final ObjectMapper mapper, @ClientId final String client, final byte[] value) {
//		this(mapper, client);
//
//
//
//		try {
//			this.payload.putAll((Map<String, BigInteger>) serializer().readValue(value, REF));
//		} catch (IOException ioe) {
//			throw new IllegalArgumentException("Unable to deserialize payload.", ioe);
//		}
//	}
//
//	private GCounter(final String client, final Map<String, BigInteger> value) {
//		this(client);
//		this.payload.putAll(value);
//	}


	//@ ensures (\forall String s; true ; other.payload.get(s).compareTo(\old(payload.get(s))) == 1 ? this.payload.get(s).equals(other.payload.get(s)) : this.payload.get(s).equals(\old(payload.get(s))) );
	//@ ensures clientId.equals(\old(clientId));
	public Void merge(GCounter other) {
		// Merge method changed to return Void instead of GCounter
		Map<String, BigInteger> retmap = Maps
				.newHashMapWithExpectedSize(Math.max(payload.size(), other.payload.size()));
		retmap.putAll(payload);

		for (Map.Entry<String, BigInteger> o : other.payload.entrySet()) {
			BigInteger value = Objects.firstNonNull(retmap.get(o.getKey()), BigInteger.ZERO);
			retmap.put(o.getKey(), o.getValue().max(value));
		}

		return null;
	}


	//TODO: How to iterate over the values of payload?
	//@ assignable \nothing;
	//@ ensures \result.intValue() == (\sum int i; i >= 0 && i < InvariantUtils.numOfReplicas(); payload.get(KEYS[i));
	public BigInteger value() {
		BigInteger retval = BigInteger.ZERO;
		for (BigInteger o : payload.values()) {
			retval = retval.add(o);
		}
		return retval;
	}

	//@ assignable this.payload.get(clientId);
	//@ ensures this.payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(1))));
	//@ ensures \result.equals(this.value());
	public BigInteger increment() {
		return this.increment(1);
	}

	//@ requires n >= 0;
	//@ assignable this.payload.get(clientId);
	//@ ensures this.payload.get(clientId).equals(\old(payload.get(clientId).add(BigInteger.valueOf(n))));
	//@ ensures \result.equals(this.value());
	public BigInteger increment(final int n) {
		Preconditions.checkArgument(n >= 0);
		BigInteger retval = payload.get(clientId).add(BigInteger.valueOf(n));
		payload.put(clientId, retval);
		return this.value();
	}

	//@ requires false;
	public byte[] payload() {
//		try {
//			return serializer().writeValueAsBytes(payload);
//		} catch (IOException ioe) {
//			throw new IllegalStateException("Cannot serialize payload.");
//		}
		return null;
	}

	//@ requires false;
	public BigInteger decrement() {
		throw new UnsupportedOperationException();
	}

	//@ requires false;
	public BigInteger decrement(final int n) {
		throw new UnsupportedOperationException();
	}


	//TODO: How to handle equals?
	//@ requires false;
	//@ assignable \nothing;
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


	//TODO: How to handle hashCode?
	//@ requires false;
	//@ assignable \nothing;
	//@ ensures \result == this.value().hashCode();
	public int hashCode() {
		return this.value().hashCode();
	}

}
