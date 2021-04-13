package de.tuda.stg.consys.integrationtest;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.Cassandra;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

public class Demo {

    public static class Box implements Serializable {
        private int i = 0;
        public void inc() {
            i++;
        }
        public int get() {
            return i;
        }
    }



    public static void main(String[] args) {
        Cassandra.ReplicaBinding replica1 = Cassandra.newReplica(
                "127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true
        );

        Cassandra.ReplicaBinding replica2 = Cassandra.newReplica(
                "127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false
        );

//		Akka.ReplicaBinding replica1 = Akka.newReplica(
//				"127.0.0.1", 4121, 2181,
//				Arrays.asList(
//						Address.apply("127.0.0.1", 4121),
//						Address.apply("127.0.0.2", 4122)
//				),
//				Duration.apply(60, "s")
//		);
//
//		Akka.ReplicaBinding replica2 = Akka.newReplica(
//				"127.0.0.2", 4122, 2182,
//				Arrays.asList(
//						Address.apply("127.0.0.1", 4121),
//						Address.apply("127.0.0.2", 4122)
//				),
//				Duration.apply(60, "s")
//		);


        System.out.println("transaction 1");
        replica1.transaction(ctx -> {
            Ref<@Strong Box> box1 = ctx.replicate("box1", CassandraConsistencyLevels.STRONG(), (Class<@Strong Box>) Box.class);
            box1.ref().inc();
            return Option.apply(2);
        });

        System.out.println("transaction 2");
        replica1.transaction(ctx -> {
            Ref<@Strong Box> box1 = ctx.lookup("box1", CassandraConsistencyLevels.STRONG(), (Class<@Strong Box>) Box.class);
            box1.ref().inc();

            int i = box1.ref().get();
            System.out.println(i);
            return Option.empty();
        });

        try {
            replica1.close();
            replica2.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
