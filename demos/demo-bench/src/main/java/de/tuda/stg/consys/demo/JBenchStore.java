package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akka.AkkaReplica;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.concurrent.duration.FiniteDuration;

public abstract class JBenchStore<StoreType extends Store> {

    private final BarrierStore scalaStore;
    private final StoreType javaStore;

    private JBenchStore(BarrierStore scalaStore, StoreType javaStore) {
        this.scalaStore = scalaStore;
        this.javaStore = javaStore;
    }

    public StoreType javaStore() {
        return javaStore;
    }

    public StoreType store() {
        return javaStore;
    }

    public BarrierStore scalaStore() {
        return scalaStore;
    }

    public void barrier(String name, int count, FiniteDuration duration) {
        scalaStore.barrier(name, count, duration);
    }


    public abstract ConsistencyLevel getWeakLevel();

    public abstract ConsistencyLevel getStrongLevel();


    public static JBenchStore<AkkaStoreBinding> fromAkkaStore(AkkaStore store) {
        var storeBinding = AkkaReplica.create(store);

        return new JBenchStore<>(store, storeBinding) {
            @Override
            public ConsistencyLevel getWeakLevel() {
                return AkkaConsistencyLevels.WEAK;
            }

            @Override
            public ConsistencyLevel getStrongLevel() {
                return AkkaConsistencyLevels.STRONG;
            }
        };
    }

    public static JBenchStore<CassandraStoreBinding> fromCassandraStore(CassandraStore store) {
        var storeBinding = CassandraReplica.create(store);

        return new JBenchStore<>(store, storeBinding) {
            @Override
            public ConsistencyLevel getWeakLevel() {
                return CassandraConsistencyLevels.WEAK;
            }

            @Override
            public ConsistencyLevel getStrongLevel() {
                return CassandraConsistencyLevels.STRONG;
            }
        };
    }
}
