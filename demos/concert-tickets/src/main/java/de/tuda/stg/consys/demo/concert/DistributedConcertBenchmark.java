package de.tuda.stg.consys.demo.concert;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.concert.schema.*;
import de.tuda.stg.consys.objects.japi.JRef;

import java.util.Date;

public class DistributedConcertBenchmark extends DemoBenchmark {

    public static void main(String[] args) {
        start(DistributedConcertBenchmark.class, args[0]);
    }


    private JRef<Concert> concert;

    private final int numOfTransactions;

    public DistributedConcertBenchmark(Config config) {
        super(config);
        numOfTransactions = config.getInt("consys.bench.demo.concert.transactions");
    }


    @Override
    public void setup() {
        if (processId() == 0) {
            JRef<ConcertHall> concertHall = replicaSystem().replicate(new ConcertHall(5), getStrongLevel());
            JRef<Band> band = replicaSystem().replicate(new Band("some band"), getWeakLevel());
            JRef<Counter> soldTickets = replicaSystem().replicate(new Counter(0), getStrongLevel());
            concert = replicaSystem().replicate("concert", new Concert(new Date(), concertHall, band, soldTickets), getStrongLevel());
        } else {
            concert = replicaSystem().lookup("concert", Concert.class, getStrongLevel());
            concert.syncAll();
        }

    }

    @Override
    public void iteration() {
        for (int i = 0; i < numOfTransactions; i++) {
            concert.ref().buyTicket();
            concert.syncAll();
            DemoUtils.printProgress(i);
        }
        DemoUtils.printDone();

    }

    @Override
    public void cleanup() {
        replicaSystem().clear();
    }
}
