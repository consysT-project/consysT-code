package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.Consensus;
import de.tuda.stg.consys.demo.invariantdemos.schema.consensus.ConsensusSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.roundcounter.ResettableCounterSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.roundcounter.ResettableCounterWithRound;
import scala.Option;

public class ResettableCounterBenchmark extends InvariantDemosBenchmark<ResettableCounterWithRound> {

    public static void main(String[] args) {
        start(ResettableCounterBenchmark.class, args);
    }

    public ResettableCounterBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super("resettablecounter", config, outputResolver, new ResettableCounterSchema());
    }
}
