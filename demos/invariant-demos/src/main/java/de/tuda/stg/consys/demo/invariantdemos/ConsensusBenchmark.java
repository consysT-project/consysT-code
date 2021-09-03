package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.Consensus;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.ConsensusSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLock;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLockSchema;
import scala.Option;

public class ConsensusBenchmark extends InvariantDemosBenchmark<Consensus> {

    public static void main(String[] args) {
        start(ConsensusBenchmark.class, args);
    }

    public ConsensusBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver, new ConsensusSchema());
    }
}
