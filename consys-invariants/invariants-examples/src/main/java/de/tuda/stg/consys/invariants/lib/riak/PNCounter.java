package de.tuda.stg.consys.invariants.lib.riak;


import com.google.common.base.Preconditions;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.math.BigInteger;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;

/**
 * Counter that supports both positive and negative operations.
 *
 */
@ReplicatedModel public class PNCounter {
	private static final String POSITIVE_TOKEN = "p";
	private static final String NEGATIVE_TOKEN = "n";
	
	private final GCounter positive;
	private final GCounter negative;

	private final String clientId;


	//@ ensures clientId.equals(client);
	//@ ensures positive.value().equals(BigInteger.ZERO);
	//@ ensures negative.value().equals(BigInteger.ZERO);
	public PNCounter(final String client) {
		this.clientId = client;
		positive = new GCounter(client);
		negative = new GCounter(client);
	}



	//@ ensures stateful(positive.merge(other.positive));
	//@ ensures stateful(negative.merge(other.negative));
	//@ ensures clientId.equals(\old(clientId));
	public Void merge(final PNCounter other) { // Change from the origin: void <- PNCounter
		positive.merge(other.positive);
		negative.merge(other.negative);
		return null;
	}


	//@ assignable \nothing;
	//@ ensures \result.equals(positive.value().subtract(negative.value()));
	@SideEffectFree @WeakOp
	public BigInteger value() {
		return this.positive.value().subtract(this.negative.value());
	}

	@SideEffectFree @WeakOp public byte[] payload() {
//		try {
//			Map<String, JsonNode> retval = Maps.newHashMap();
//
//			retval.put(POSITIVE_TOKEN, serializer().readTree(positive.payload()));
//			retval.put(NEGATIVE_TOKEN, serializer().readTree(negative.payload()));
//
//			return serializer().writeValueAsBytes(retval);
//		} catch (IOException ioe) {
//			throw new IllegalStateException("Could not serialize.", ioe);
//		}
		return null;
	}


	//@ assignable positive;
	//@ ensures stateful(positive.increment());
	//@ ensures \result.equals(this.value());
	@WeakOp public BigInteger increment() {
		this.positive.increment();

		return this.value();
	}


	//@ requires n >= 0;
	//@ assignable positive;
	//@ ensures stateful(positive.increment(n));
	//@ ensures \result.equals(this.value());
	@WeakOp public BigInteger increment(final int n) {
		Preconditions.checkArgument(n >= 0);
		this.positive.increment(n);
		return this.value();
	}

	//@ assignable negative;
	//@ ensures stateful(negative.increment());
	//@ ensures \result.equals(this.value());
	@WeakOp public BigInteger decrement() {
		this.negative.increment();
		return this.value();
	}


	//@ requires n >= 0;
	//@ assignable negative;
	//@ ensures stateful(negative.increment(n));
	//@ ensures \result.equals(this.value());
	@WeakOp public BigInteger decrement(final int n) {
		Preconditions.checkArgument(n >= 0);
		
		this.negative.increment(n);

		return this.value();
	}

	//TODO: How to handle equals?
	//@ requires false;
	//@ assignable \nothing;
	@SideEffectFree @WeakOp public boolean equals(final Object o) {
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

	//TODO: How to handle hashCode?
	//@ requires false;
	//@ assignable \nothing;
	//@ ensures \result == this.value().hashCode();
	@SideEffectFree @WeakOp public int hashCode() {
		return this.value().hashCode();
	}

}
