package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.Consensus;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.ConsensusSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.jointbankaccount.JointBankAccount;
import de.tuda.stg.consys.demo.invariantdemos.schema.jointbankaccount.JointBankAccountSchema;
import scala.Option;

public class JointBankAccountBenchmark extends InvariantDemosBenchmark<JointBankAccount> {

    public static void main(String[] args) {
        start(JointBankAccountBenchmark.class, args);
    }

    public JointBankAccountBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver, new JointBankAccountSchema());
    }
}
