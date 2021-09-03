package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.bankaccountlww.BankAccountLWW;
import de.tuda.stg.consys.demo.invariantdemos.schema.bankaccountlww.BankAccountLWWSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLock;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLockSchema;
import scala.Option;

public class BankAccountLWWBenchmark extends InvariantDemosBenchmark<BankAccountLWW> {

    public static void main(String[] args) {
        start(BankAccountLWWBenchmark.class, args);
    }

    public BankAccountLWWBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver, new BankAccountLWWSchema());
    }
}
