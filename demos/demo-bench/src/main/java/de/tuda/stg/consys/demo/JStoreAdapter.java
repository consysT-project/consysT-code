package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.extensions.DistributedStore;
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akka.AkkaReplica;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import scala.concurrent.duration.FiniteDuration;

public abstract class JStoreAdapter<StoreType extends Store> {

    private final BarrierStore scalaStore;
    private final StoreType javaStore;

    private JStoreAdapter(BarrierStore scalaStore, StoreType javaStore) {
        this.scalaStore = scalaStore;
        this.javaStore = javaStore;
    }

    public StoreType store() {
        return javaStore;
    }

    public void barrier(String name, int count, FiniteDuration duration) {
        scalaStore.barrier(name, count, duration);
    }


    public abstract ConsistencyLevel getWeakLevel();

    public abstract ConsistencyLevel getStrongLevel();


    public static JStoreAdapter<AkkaStoreBinding> akkaAdapter(AkkaStore store) {
        var storeBinding = AkkaReplica.create(store);

        return new JStoreAdapter<>(store, storeBinding) {
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
}
