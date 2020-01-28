package compiler;

import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.next.cassandra.Binding;
import de.tuda.stg.consys.japi.next.Ref;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class TestClass {

	public static class Box implements Serializable {
		public int i;
		public Box(int i) {
			this.i = i;
		}
		public int incBy(int amount) {
			i += amount;
			return i;
		}
	}

//	public static void main(String[] args) throws Exception {
//
//		JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);
//
//		JReplicaSystem replicaSystem1 = systems[0];
//		JReplicaSystem replicaSystem2 = systems[1];
//
//		try {
//			JRef<Box> ref1Strong = replicaSystem1.replicate("os", new Box(42), JConsistencyLevels.STRONG);
//			JRef<Box> ref2Strong = replicaSystem2.lookup("os", Box.class, JConsistencyLevels.STRONG);
//
//			ref1Strong.ref().incBy(23);
//			System.out.println(Objects.toString(ref2Strong.ref().i));
//			ref2Strong.ref().i = 777;
//			System.out.println(Objects.toString(ref1Strong.ref().i));
//
//			ref2Strong.ref().i = ref2Strong.ref().i;
//
//		} finally {
//			replicaSystem1.close();
//			replicaSystem2.close();
//		}
//
//	}


	public static void main(String[] args) throws Exception {
		Binding.Cassandra.ReplicaBinding replica1 = Binding.Cassandra.newReplica(
			"127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true
		);

		Binding.Cassandra.ReplicaBinding replica2 = Binding.Cassandra.newReplica(
			"127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false
		);

		System.out.println("transaction 1");
		replica1.transaction(ctx -> {
			Ref<Box> box1 = ctx.replicate("box1", new Box(42), CassandraConsistencyLevels.STRONG());
			box1.ref().incBy(23);
			System.out.println("inced");
			return Option.empty();
		});

		System.out.println("done.");

//		System.out.println("transaction 2");
//		replica1.transaction(ctx -> {
//			Ref<Box> box1 = ctx.lookup("box1", Box.class, CassandraConsistencyLevels.STRONG());
//			box1.ref().incBy(1);
//			int i = box1.ref().i;
//			System.out.println(i);
//			return Option.empty();
//		});

		replica1.close();
		replica2.close();

	}


}
