package com.readytalk.crdt.counters;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.utils.InvariantUtils.*;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Map;

import javax.annotation.Nonnegative;
import javax.inject.Inject;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;
import com.readytalk.crdt.AbstractCRDT;
import com.readytalk.crdt.inject.ClientId;

/**
 * Counter that supports both positive and negative operations.
 *
 */
@ReplicatedModel public class PNCounter extends AbstractCRDT<BigInteger, PNCounter> implements CRDTCounter<BigInteger, PNCounter> {
	// Can we say when we are sure about GCounter, we can omit GCounter related conditions? Yes!

	// Change from the origin: We had this field:
	//private static final TypeReference<Map<String, JsonNode>> REF = new TypeReference<Map<String, JsonNode>>() {
	//};
	
	
	private static final String POSITIVE_TOKEN = "p";
	private static final String NEGATIVE_TOKEN = "n";
	
	private final GCounter positive;
	private final GCounter negative;

	private final String clientId;

	// Any need to check GCounters are zero?
	/*@
	@ ensures clientId.equals(client);
	@ ensures positive.value().equals(BigInteger.ZERO);
	@ ensures negative.value().equals(BigInteger.ZERO);
	@*/
	@Inject
	public PNCounter(final ObjectMapper mapper, @ClientId final String client) {
		super(mapper);

		this.clientId = client;

		positive = new GCounter(mapper, client);
		negative = new GCounter(mapper, client);

	}

	/* Change from the origin: We had this constructor:
	public PNCounter(final ObjectMapper mapper, @ClientId final String client, final byte[] value) {
		super(mapper);

		this.clientId = client;

		try {
			
			Map<String, JsonNode> retval = mapper.readValue(value, REF);

			positive = new GCounter(mapper, client, mapper.writeValueAsBytes(retval.get(POSITIVE_TOKEN)));
			negative = new GCounter(mapper, client, mapper.writeValueAsBytes(retval.get(NEGATIVE_TOKEN)));

		} catch (IOException ioe) {
			throw new IllegalArgumentException("Invalid JSON", ioe);
		}

	}
	End change from the origin */

	private PNCounter(final ObjectMapper mapper, @ClientId final String client, final GCounter p, final GCounter n) {
		super(mapper);

		positive = p;
		negative = n;

		this.clientId = client;
	}

	/* Old postconditions:
	ensures positive.equals(\old(positive).merge(other.positive));
	ensures negative.equals(\old(negative).merge(other.negative));
	*/
	/*@
	@ ensures stateful(positive.merge(other.positive));
	@ ensures stateful(negative.merge(other.negative));
	@ ensures clientId.equals(\old(clientId));
	@*/
	// changed from original: @Override
	public Void merge(final PNCounter other) { // Change from the origin: void <- PNCounter
		// my codes:
		positive.merge(other.positive);
		negative.merge(other.negative);
		// end of my codes.
		// this merge function had GCounter output type.
		//return new PNCounter(serializer(), clientId, positive.merge(other.positive), negative.merge(other.negative));
	}
	/*@
	@ assignable \nothing;
	@ ensures \result.equals(positive.value().subtract(negative.value()));
	@*/
	// changed from original: @Override
	public BigInteger value() {
		return this.positive.value().subtract(this.negative.value());
	}

	// changed from original: @Override
	public byte[] payload() {
		try {
			Map<String, JsonNode> retval = Maps.newHashMap();

			retval.put(POSITIVE_TOKEN, serializer().readTree(positive.payload()));
			retval.put(NEGATIVE_TOKEN, serializer().readTree(negative.payload()));

			return serializer().writeValueAsBytes(retval);
		} catch (IOException ioe) {
			throw new IllegalStateException("Could not serialize.", ioe);
		}
	}

	// The old post condition: positive.value().equals(\old(positive.value()).add(BigInteger.valueOf(1)));
	/*@
	@ assignable positive;
	@ ensures stateful(positive.increment());
	@ ensures \result.equals(this.value());
	@*/
	// changed from original: @Override
	public BigInteger increment() {
		this.positive.increment();

		return this.value();
	}

	// The old post condition: positive.value().equals(\old(positive.value()).add(BigInteger.valueOf(n)));
	/*@
	@ requires n >= 0;
	@ assignable positive;
	@ ensures stateful(positive.increment(n));
	@ ensures \result.equals(this.value());
	@*/
	// changed from original: @Override
	public BigInteger increment(@Nonnegative final int n) {
		Preconditions.checkArgument(n >= 0);
		
		this.positive.increment(n);

		return this.value();
	}

	// The old post condition: negative.value().equals(\old(negative.value()).add(BigInteger.valueOf(1)));
	/*@
	@ assignable negative;
	@ ensures stateful(negative.increment());
	@ ensures \result.equals(this.value());
	@*/
	// changed from original: @Override
	public BigInteger decrement() {
		this.negative.increment();

		return this.value();
	}

	// The old post condition: negative.value().equals(\old(negative.value()).add(BigInteger.valueOf(n)));
	/*@
	@ requires n >= 0;
	@ assignable negative;
	@ ensures stateful(negative.increment(n));
	@ ensures \result.equals(this.value());
	@*/
	// changed from original: @Override
	public BigInteger decrement(@Nonnegative final int n) {
		Preconditions.checkArgument(n >= 0);
		
		this.negative.increment(n);

		return this.value();
	}

	// Prevously: \result == o.value().equals(this.value());
	// The problem was type casting but we conclude we don't need any post conditions in equals method.
	/*@
	@ assignable nothing;
	@*/
	// changed from original: @Override
	public boolean equals(final Object o) {
		if (!(o instanceof PNCounter)) {
			return false;
		}

		PNCounter t = (PNCounter) o;

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
	public int hashCode() {
		return this.value().hashCode();
	}

}
