package de.tuda.stg.consys.japi;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class CassandraDemo {

	public static @Mixed class Box implements Serializable {
		public int i = 0;

		@StrongOp
		public void inc() {
			i++;
		}

		@WeakOp
		public int get() {
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
			Ref<Box> box1 = ctx.replicate("box1", CassandraConsistencyLevels.MIXED, Box.class);
			box1.invoke("inc"); //No compiler plugin => we have to use this syntax
			return Option.apply(2);
		});

		System.out.println("transaction 2");
		replica1.transaction(ctx -> {
			Ref<Box> box1 = ctx.lookup("box1", CassandraConsistencyLevels.MIXED, Box.class);
			box1.invoke("inc");
			int i = box1.invoke("get");
			System.out.println(i);
			return Option.empty();
		});

		replica1.close();
		replica2.close();
	}

}
