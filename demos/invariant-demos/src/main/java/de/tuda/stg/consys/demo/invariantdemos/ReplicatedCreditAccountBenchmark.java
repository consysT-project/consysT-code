package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount.ReplicatedCreditAccount;
import de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount.ReplicatedCreditAccountSchema;
import de.tuda.stg.consys.japi.legacy.JRef;
import scala.Option;

public class ReplicatedCreditAccountBenchmark extends InvariantDemosBenchmark<ReplicatedCreditAccount> {

    public static void main(String[] args) {
        start(ReplicatedCreditAccountBenchmark.class, args);
    }

    public ReplicatedCreditAccountBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super("creditaccount", config, outputResolver, new ReplicatedCreditAccountSchema());
    }
}
