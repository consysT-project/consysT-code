package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.core.store.extensions.store.LockingStore;
import de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount.ReplicatedCreditAccount;
import de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount.ReplicatedCreditAccountSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLock;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLockSchema;
import scala.Option;

public class DistributedLockBenchmark extends InvariantDemosBenchmark<DistributedLock> {

    public static void main(String[] args) {
        start(DistributedLockBenchmark.class, args);
    }

    public DistributedLockBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super("distributedlock", config, outputResolver, new DistributedLockSchema());
    }
}
