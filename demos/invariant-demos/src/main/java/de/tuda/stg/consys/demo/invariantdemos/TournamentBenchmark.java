package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLock;
import de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock.DistributedLockSchema;
import de.tuda.stg.consys.demo.invariantdemos.schema.tournament.Tournaments;
import de.tuda.stg.consys.demo.invariantdemos.schema.tournament.TournamentsSchema;
import scala.Option;

public class TournamentBenchmark extends InvariantDemosBenchmark<Tournaments> {

    public static void main(String[] args) {
        start(TournamentBenchmark.class, args);
    }

    public TournamentBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super("tournament", config, outputResolver, new TournamentsSchema());
    }
}
