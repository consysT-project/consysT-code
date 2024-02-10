package de.tuda.stg.consys.japi;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.japi.binding.akka.AkkaReplica;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

import java.io.Serializable;
import java.util.Set;

import static de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels.STRONG;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class AkkaDemo {

	public static class GSet implements Serializable, Mergeable<GSet> {
		private Set<Integer> underlying = Sets.newHashSet();

		public void add(int elem) {
			underlying.add(elem);
		}

		public Set<Integer> getUnderlying() {
			return underlying;
		}

		@Override
		public Void merge(GSet other) {
			underlying.addAll(other.underlying);
			return null;
		}
	}

	public static void main(String[] args) throws Exception {

		ConsistencyLevel<AkkaStore> exampleConsistency = STRONG;

		AkkaStoreBinding replica1 = AkkaReplica.create(
			"127.0.0.1", 4445, 2181
		);

		AkkaStoreBinding replica2 = AkkaReplica.create(
			"127.0.0.2", 4446, 2182
		);


		replica1.addOtherReplica("127.0.0.2", 4446);
		replica2.addOtherReplica("127.0.0.1", 4445);


		Logger.info("transaction 1");
		replica1.transaction(ctx -> {
			Ref<GSet> set1 = ctx.replicate("set1", exampleConsistency, GSet.class);
			set1.invoke("add", 42);
			set1.invoke("add", 23);
			return Option.apply(0);
		});

		Logger.info("transaction 2");
		replica2.transaction(ctx -> {
			Ref<GSet> set1 = ctx.lookup("set1", exampleConsistency, GSet.class);
			set1.invoke("add", 43);
			set1.invoke("add", 24);
			return Option.apply(0);
		});

		Logger.info("transaction 3");
		var result  = replica1.transaction(ctx -> {
			Ref<GSet> set1 = ctx.lookup("set1", exampleConsistency, GSet.class);
			var underlying = set1.<Set<Integer>>invoke("getUnderlying");
			return Option.apply(underlying);
		});

		Logger.info("result: " + result);

		replica1.close();
		replica2.close();
	}

}
