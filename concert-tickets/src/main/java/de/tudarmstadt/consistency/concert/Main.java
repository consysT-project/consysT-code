package de.tudarmstadt.consistency.concert;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.java.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.java.JRef;

import java.util.Date;

import static de.tudarmstadt.consistency.concert.Replicas.replicaSystem1;
import static de.tudarmstadt.consistency.concert.Replicas.replicaSystem2;

public class Main {
	public static void main(String... args) throws Exception {
        JRef<@Strong ConcertHall> concertHall = replicaSystem1.replicate(new ConcertHall(5), JConsistencyLevel.STRONG);
        JRef<@Weak Band> band = replicaSystem1.replicate(new Band("some band"), JConsistencyLevel.WEAK);
        JRef<@Strong Counter> soldTickets = replicaSystem1.replicate(new Counter(0), JConsistencyLevel.STRONG);
        JRef<@Strong Concert> concert1 = replicaSystem1.replicate("concert", new Concert(new Date(), concertHall, band, soldTickets), JConsistencyLevel.STRONG);

        JRef<@Strong Concert> concert2 = replicaSystem2.ref("concert", Concert.class, JConsistencyLevel.STRONG);

        Thread.sleep(1000);

        System.out.println(
                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
        System.out.println(
                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");

        System.out.println("-> change band name");
        concert1.<JRef<@Weak Band>>getField("band").setField("name", "some other band");

        System.out.println("-> buy ticket");
        concert1.invoke("buyTicket");

        System.out.println(
                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
        System.out.println(
                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");

        System.out.println("-> sync band");
        concert2.<JRef<@Weak Band>>getField("band").sync();

        System.out.println(
                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
        System.out.println(
                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");
	}
}
