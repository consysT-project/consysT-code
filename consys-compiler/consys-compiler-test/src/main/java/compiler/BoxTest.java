package compiler;

import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class BoxTest {

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


	public static void main(String[] args) throws Exception {
		CassandraStoreBinding replica1 = CassandraReplica.create(
			"127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true
		);

		CassandraStoreBinding replica2 = CassandraReplica.create(
			"127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false
		);

		System.out.println("transaction 1");
		replica1.transaction(ctx -> {
			Ref<Box> box1 = ctx.replicate("box1",  CassandraConsistencyLevels.STRONG, Box.class, 42);
			box1.ref().incBy(23);
			System.out.println("inced");
			return Option.empty();
		});

		System.out.println("done.");

		System.out.println("transaction 2");
		replica1.transaction(ctx -> {
			Ref<Box> box1 = ctx.lookup("box1", CassandraConsistencyLevels.STRONG, Box.class);
			box1.ref().incBy(1);
			int i = box1.ref().i;
			System.out.println(i);
			return Option.empty();
		});

		replica1.close();
		replica2.close();
	}
}
