package de.tuda.stg.consys.demo.concert;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.concert.schema.*;
import de.tuda.stg.consys.japi.JRef;

import java.util.Date;
import java.util.Random;

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

    private final Random random = new Random();

    @Override
    public void setup() {
        if (processId() == 0) {
            JRef<ConcertHall> concertHall = replicaSystem().replicate(new ConcertHall(5), getStrongLevel());
            JRef<Band> band = replicaSystem().replicate(new Band("some band"), getWeakLevel());
            JRef<Counter> soldTickets = replicaSystem().replicate(new Counter(0), getStrongLevel());
            JRef<BuyTicket> buyer = replicaSystem().replicate(new BuyTicket(concertHall, soldTickets), getStrongLevel());

            concert = replicaSystem().replicate("concert", new Concert(new Date(), concertHall, band, soldTickets, buyer), getWeakLevel());
        } else {
            concert = replicaSystem().lookup("concert", Concert.class, getWeakLevel());
            concert.syncAll();
        }

    }

    @Override
    public void operation() {
        if (processId() != 0) {
            for (int i = 0; i < numOfTransactions; i++) {
                concert.ref().buyTicket();
                if (random.nextInt(100) < 20) concert.syncAll();
                DemoUtils.printProgress(i);
            }
            DemoUtils.printDone();
        }
    }

    private void randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 58) {
            transaction2();
        } else if (rand < 80) {
            transaction3();
        } else if (rand < 100) {
            transaction1();
        }
    }

    private void transaction1() {
        concert.ref().buyTicket();
    }

    private void transaction2() {
        concert.ref().getBandName();
        if (random.nextInt(100) < 20) concert.sync();
    }

    private void transaction3() {
        concert.ref().getDate();
        if (random.nextInt(100) < 20) concert.sync();
    }

    @Override
    public void cleanup() {
        replicaSystem().clear();
    }
}
