package de.tudarmstadt.consistency.concert;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.ConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;
import de.tudarmstadt.consistency.replobj.japi.JReplicaSystem;

import java.util.Date;

public class MainDeployment {
    public static void main(String... args) throws Exception {
        String localname = args.length < 1 ? "127.0.0.1" : args[0];
        String remotename = args.length < 2 ? "127.0.0.1" : args[1];
        boolean first = args.length < 3 || args[2].equals("strong:0") || args[2].equals("weak:0");

        System.out.println("SETUP: starting local replica system on port " + localname + ":" + (first ? 2552 : 2553));

        JReplicaSystem replicaSystem = JReplicaSystem.fromActorSystem(localname, first ? 2552 : 2553);

        int i = 0;
        while (true) {
            Thread.sleep(1000);
            i++;
            try {
                replicaSystem.addReplicaSystem(remotename, first ? 2553 : 2552);
                break;
            }
            catch (Exception e) {
                if (i == 60)
                    throw e;
            }
        }

        System.out.println("SETUP: connected to remote replica system on " + remotename + ":" + (first ? 2553 : 2552));

        if (args.length > 2)
            switch (args[2]) {
                case "strong:0": {
                    JRef<@Strong ConcertHall> concertHall = replicaSystem.replicate(new ConcertHall(5), JConsistencyLevel.STRONG);
                    JRef<@Weak Band> band = replicaSystem.replicate(new Band("some band"), JConsistencyLevel.WEAK);
                    JRef<@Strong Counter> soldTickets = replicaSystem.replicate(new Counter(0), JConsistencyLevel.STRONG);
                    replicaSystem.replicate("concert", new ConcertStrongAuto(new Date(), concertHall, band, soldTickets), JConsistencyLevel.STRONG);
                }
                break;

                case "weak:0": {
                    JRef<@Weak ConcertHall> concertHall = replicaSystem.replicate(new ConcertHall(5), JConsistencyLevel.WEAK);
                    JRef<@Weak Band> band = replicaSystem.replicate(new Band("some band"), JConsistencyLevel.WEAK);
                    JRef<@Weak Counter> soldTickets = replicaSystem.replicate(new Counter(0), JConsistencyLevel.WEAK);
                    replicaSystem.replicate("concert", new ConcertWeak(new Date(), concertHall, band, soldTickets), JConsistencyLevel.WEAK);
                }
                break;

                case "strong:1":
                    measure(replicaSystem, "concert", ConcertStrongAuto.class, JConsistencyLevel.STRONG);
                break;

                case "weak:1":
                    measure(replicaSystem, "concert", ConcertWeak.class, JConsistencyLevel.WEAK);
                break;
            }
    }

    private static <T> void measure(JReplicaSystem replicaSystem, String addr, Class<T> objCls, ConsistencyLevel consistencyLevel) throws Exception {
        System.out.println("SETUP: looking up \"" + addr + "\"");

        JRef<T> concert = replicaSystem.ref(addr, objCls, consistencyLevel);

        int i = 0;
        while (true) {
            Thread.sleep(1000);
            i++;
            try {
                concert.invoke("buyTicket");
                break;
            }
            catch (Exception e) {
                if (i == 60)
                    throw e;
            }
        }

        System.out.println("SETUP: measurement setup successful");

        int count = 1000;

        // warmup
        for (i = 0; i < count; i++)
            concert.invoke("buyTicket");

        // measurement
        long start = System.nanoTime();
        for (i = 0; i < count; i++)
            concert.invoke("buyTicket");
        long end = System.nanoTime();

        System.out.println("Average running time for one `buyTicket` invocation over " + count + " invocations: " + ((end - start) / 1000000.0 / count) + "ms");
    }
}
