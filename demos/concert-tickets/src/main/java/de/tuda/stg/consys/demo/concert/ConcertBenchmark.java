package de.tuda.stg.consys.demo.concert;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.concert.schema.*;
import de.tuda.stg.consys.japi.legacy.JRef;
import scala.Option;

import java.util.Date;
import java.util.Random;

public class ConcertBenchmark extends DemoBenchmark {

    public static void main(String[] args) {
        start(ConcertBenchmark.class, args);
    }

    private JRef<Concert> concert;

    public ConcertBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);
    }

    private final Random random = new Random();

    @Override
    public void setup() {
        if (processId() == 0) {
            JRef<ConcertHall> concertHall = system().replicate(new ConcertHall(5), getStrongLevel());
            JRef<Band> band = system().replicate(new Band("some band"), getWeakLevel());
            JRef<Counter> soldTickets = system().replicate(new Counter(0), getStrongLevel());
            JRef<BuyTicket> buyer = system().replicate(new BuyTicket(concertHall, soldTickets), getStrongLevel());

            concert = system().replicate("concert", new Concert(new Date(), concertHall, band, soldTickets, buyer), getWeakLevel());
        } else {
            concert = system().lookup("concert", Concert.class, getWeakLevel());
            concert.syncAll();
        }

    }

    @Override
    public void operation() {
        if (processId() != 0) {
            concert.ref().buyTicket();
            doSync(() -> concert.syncAll());
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
        doSync(() -> {
            JRef<BuyTicket> buyer = concert.ref().buyer;
            JRef<Counter> counter = buyer.ref().soldTickets;
            counter.sync();
        });
    }

    private void transaction2() {
        concert.ref().getBandName();
    }

    private void transaction3() {
        concert.ref().getDate();
    }

    @Override
    public void cleanup() {
        system().clear();
    }
}
