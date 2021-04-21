package de.tuda.stg.consys.integrationtest;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
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


    static abstract class DemoRunner<
            Stor extends de.tuda.stg.consys.core.store.Store,
            Level extends ConsistencyLevel<Stor>,
            Tx extends  TransactionContext<String, Serializable, Level>,
            ReplicaBinding extends Store<String, Serializable, Level, Tx>
            > implements Runnable {

        final ReplicaBinding replica1;
        final ReplicaBinding replica2;

        DemoRunner(ReplicaBinding replica1, ReplicaBinding replica2) {
            this.replica1 = replica1;
            this.replica2 = replica2;
        }

        abstract Level level();

        @Override
        @SuppressWarnings("consistency") /* Turn off type checker */
        public void run() {
            System.out.println("transaction 1");
            replica1.transaction(ctx -> {
                Ref<@Strong Box> box1 = ctx.replicate("box1", level(), (Class<@Strong Box>) Box.class);
                box1.ref().inc();
                return Option.apply(2);
            });

            System.out.println("transaction 2");
            replica1.transaction(ctx -> {
                Ref<@Strong Box> box1 = ctx.lookup("box1", level(), (Class<@Strong Box>) Box.class);
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

    static class CassandraRunner
            extends DemoRunner<CassandraStore, ConsistencyLevel<CassandraStore>, CassandraTransactionContextBinding, CassandraStoreBinding> {

        CassandraRunner() {
            super(
                Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true),
                Cassandra.newReplica("127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false)
            );
        }

        @Override
        ConsistencyLevel<CassandraStore> level() {
            return CassandraConsistencyLevels.STRONG;
        }
    }

//    static class AkkaRunner extends DemoRunner<Akka.TransactionContextBinding, Akka.ReplicaBinding> {
//        AkkaRunner() {
//            super(
//                Akka.newReplica(
//                    "127.0.0.1", 4121, 2181,
//                    Arrays.asList(
//                            Address.apply("127.0.0.1", 4121),
//                            Address.apply("127.0.0.2", 4122)
//                    ),
//                    Duration.apply(60, "s")
//		        ),
//                Akka.newReplica(
//                    "127.0.0.2", 4122, 2182,
//                    Arrays.asList(
//                            Address.apply("127.0.0.1", 4121),
//                            Address.apply("127.0.0.2", 4122)
//                    ),
//                    Duration.apply(60, "s")
//                ));
//        }
//    }


    public static void main(String[] args) {
        new CassandraRunner().run();
    }
}
