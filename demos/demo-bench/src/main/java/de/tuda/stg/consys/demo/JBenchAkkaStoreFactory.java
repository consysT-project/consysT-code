package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;

public class JBenchAkkaStoreFactory implements JBenchStoreFactory<AkkaStore, AkkaStoreBinding> {
    @Override
    public JBenchStore<AkkaStoreBinding> create(AkkaStore store) {
        return JBenchStore.fromAkkaStore(store);
    }
}
