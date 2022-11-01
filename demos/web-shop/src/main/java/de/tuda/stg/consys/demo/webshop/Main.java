package de.tuda.stg.consys.demo.webshop;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.webshop.schema.MyProduct;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

public class Main {
    static abstract class DemoRunner<
            MyStore extends de.tuda.stg.consys.core.store.Store,
            Level extends ConsistencyLevel<MyStore>,
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
        public void run() {

           System.out.println("transaction 1");

            replica1.transaction(ctx -> {
                Ref<@Weak MyProduct> product1 = ctx.replicate("product1", level(), (Class<@Weak MyProduct>) MyProduct.class,  9);

                Ref<@Strong MyProduct> product2 = ctx.replicate("product2", level(), (Class<@Strong MyProduct>) MyProduct.class,  5);

                // shouldn't this lead to a type error? due to disallowed information-flow from weak to strong
                if (product1.ref().getQuantity() < 10) {
                    product2.ref().reduceQuantity(2);
                }

                return Option.apply(product1);
            });

            System.out.println("transaction 2");
            replica1.transaction(ctx -> {
                Ref<@Weak MyProduct> product1 = ctx.lookup("product1", level(), (Class<@Weak MyProduct>) MyProduct.class);
                System.out.println(product1.ref().getQuantity());
                product1.ref().reduceQuantity(5);
                System.out.println(product1.ref().getQuantity());
                return Option.apply(product1);
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
                    CassandraReplica.create("127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true),
                    CassandraReplica.create("127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false)
            );
        }

        @Override
        ConsistencyLevel<CassandraStore> level() {
            return CassandraConsistencyLevels.STRONG;
        }

    }

    public static void main(String[] args) {
        new CassandraRunner().run();
    }
}
