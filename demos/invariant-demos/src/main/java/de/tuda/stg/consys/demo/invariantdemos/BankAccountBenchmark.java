package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.bankaccount.BankAccount;
import de.tuda.stg.consys.demo.invariantdemos.schema.bankaccount.BankAccountSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLock;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLockSchema;
import scala.Option;

public class BankAccountBenchmark extends InvariantDemosBenchmark<BankAccount> {

    public static void main(String[] args) {
        start(BankAccountBenchmark.class, args);
    }

    public BankAccountBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver, new BankAccountSchema());
    }
}
