package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.japi.Store;
import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.BaseStoreBenchmark;
import de.tuda.stg.consys.core.store.extensions.DistributedStore;
import scala.Function1;

public abstract class JStoreBenchmark<StoreType extends DistributedStore> {

    private final BaseStoreBenchmark<StoreType> benchmark;
    private final Store jstore;

    public JStoreBenchmark(BaseStoreBenchmark<StoreType> benchmark) {
        this.benchmark = benchmark;
        jstore = createJStore(benchmark);
    }

    abstract protected Store createJStore(BaseStoreBenchmark<StoreType> benchmark);





}
