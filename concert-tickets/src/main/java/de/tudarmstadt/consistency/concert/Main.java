package de.tudarmstadt.consistency.concert;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.ConsistencyLevel;
import de.tudarmstadt.consistency.replobj.actors.*;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.util.Date;

import static de.tudarmstadt.consistency.concert.Replicas.replicaSystem1;
import static de.tudarmstadt.consistency.concert.Replicas.replicaSystem2;

public class Main {
	public static void main(String... args) throws Exception {
        JRef<@Weak ConcertHall> concertHall = replicaSystem1.replicate(new ConcertHall(5), JConsistencyLevel.WEAK);
        JRef<@Weak Band> band = replicaSystem1.replicate(new Band("some band"), JConsistencyLevel.WEAK);
        JRef<@Weak Counter> soldTickets = replicaSystem1.replicate(new Counter(0), JConsistencyLevel.WEAK);
        JRef<@Strong ConcertStrongManual> concert1 = replicaSystem1.replicate("concert", new ConcertStrongManual(new Date(), concertHall, band, soldTickets), JConsistencyLevel.STRONG);

        JRef<@Strong ConcertStrongManual> concert2 = replicaSystem2.ref("concert", ConcertStrongManual.class, JConsistencyLevel.STRONG);

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


        System.out.println("-> manual synchronization");


        // manually access "soldTickets"

        ReplicatedObject<@Strong ConcertStrongManual> replica1 = ReplicatedObject.from(concert2);

        AkkaReplicaSystem.GlobalContext$ context1 = replica1.internal.replicaSystem().GlobalContext();

        boolean needNewTx = !context1.hasCurrentTransaction();

        if (needNewTx) context1.startNewTransaction();

        ContextPath path = context1.getBuilder().nextPath(ConsistencyLevel.Weak$.MODULE$);

        context1.getBuilder().push(ConsistencyLevel.Weak$.MODULE$);

        Requests.RequestHandler<String> handler1 =
                replica1.internal.replicaSystem().acquireHandlerFrom(
                        replica1.master,
                        replica1.internal.replicaSystem().acquireHandlerFrom$default$2());
        StrongAkkaReplicaSystem.ReadResult readResult =
                (StrongAkkaReplicaSystem.ReadResult) handler1.request(
                        replica1.address,
                        new StrongAkkaReplicaSystem.ReadStrongField(new Requests.GetFieldOp<>(path, "soldTickets")),
                        handler1.request$default$3());
        JRef<@Weak Counter> result1 = (JRef<@Weak Counter>) readResult.res();
        handler1.close();

        replica1.system.initializeRefFieldsFor(result1);

        context1.getBuilder().pop();

        if (needNewTx) context1.endTransaction();


        // manually access "value" of "soldTickets"

        ReplicatedObject<@Strong Counter> replica2 = ReplicatedObject.from(result1);

        AkkaReplicaSystem.GlobalContext$ context2 = replica2.internal.replicaSystem().GlobalContext();

        context2.startNewTransaction();

        Requests.RequestHandler<String> handler2 =
                replica2.internal.replicaSystem().acquireHandlerFrom(
                        replica2.master,
                        replica2.internal.replicaSystem().acquireHandlerFrom$default$2());
        WeakAkkaReplicaSystem.WeakSynchronized weakSynchronized =
                (WeakAkkaReplicaSystem.WeakSynchronized) handler2.request(
                        replica2.address,
                        new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(replica2.localOperations),
                        handler2.request$default$3());
        Counter result2 = (Counter) weakSynchronized.obj();
        handler2.close();

        replica2.internal.setObject(result2);
        replica2.localOperations.clear();

        context2.endTransaction();


        System.out.println(
                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
                "concert2: " + result2.value);
    }

//    public static void main(String... args) throws Exception {
//        JRef<@Strong ConcertHall> concertHall = replicaSystem1.replicate(new ConcertHall(5), JConsistencyLevel.STRONG);
//        JRef<@Weak Band> band = replicaSystem1.replicate(new Band("some band"), JConsistencyLevel.WEAK);
//        JRef<@Strong Counter> soldTickets = replicaSystem1.replicate(new Counter(0), JConsistencyLevel.STRONG);
//        JRef<@Strong ConcertStrongAuto> concert1 = replicaSystem1.replicate("concert", new ConcertStrongAuto(new Date(), concertHall, band, soldTickets), JConsistencyLevel.STRONG);
//
//        JRef<@Strong ConcertStrongAuto> concert2 = replicaSystem2.ref("concert", ConcertStrongAuto.class, JConsistencyLevel.STRONG);
//
//        Thread.sleep(1000);
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
//        System.out.println(
//                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
//                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");
//
//        System.out.println("-> change band name");
//        concert1.<JRef<@Weak Band>>getField("band").setField("name", "some other band");
//
//        System.out.println("-> buy ticket");
//        concert1.invoke("buyTicket");
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
//        System.out.println(
//                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
//                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");
//
//
//        System.out.println("-> manual synchronization");
//
//
//        // manually access "soldTickets"
//
//        ReplicatedObject<@Strong ConcertStrongAuto> replica1 = ReplicatedObject.from(concert2);
//
//        AkkaReplicaSystem.GlobalContext$ context1 = replica1.internal.replicaSystem().GlobalContext();
//
//        boolean needNewTx = !context1.hasBuilder();
//
//        if (needNewTx) context1.startNewTransaction();
//
//        ContextPath path = context1.getBuilder().nextPath(ConsistencyLevel.Weak$.MODULE$);
//
//        context1.getBuilder().push(ConsistencyLevel.Weak$.MODULE$);
//
//        Requests.RequestHandler<String> handler1 =
//                replica1.internal.replicaSystem().acquireHandlerFrom(
//                        replica1.master,
//                        replica1.internal.replicaSystem().acquireHandlerFrom$default$2());
//        StrongAkkaReplicaSystem.ReadResult readResult =
//                (StrongAkkaReplicaSystem.ReadResult) handler1.request(
//                        replica1.address,
//                        new StrongAkkaReplicaSystem.ReadStrongField(new Requests.GetFieldOp<>(path, "soldTickets")),
//                        handler1.request$default$3());
//        JRef<@Weak Counter> result1 = (JRef<@Weak Counter>) readResult.res();
//        handler1.close();
//
//        replica1.system.initializeRefFieldsFor(result1);
//
//        context1.getBuilder().pop();
//
//        if (needNewTx) context1.endTransaction();
//
//
//        // manually access "value" of "soldTickets"
//
//        ReplicatedObject<@Strong Counter> replica2 = ReplicatedObject.from(result1);
//
//        AkkaReplicaSystem.GlobalContext$ context2 = replica2.internal.replicaSystem().GlobalContext();
//
//        context2.startNewTransaction();
//
//        Requests.RequestHandler<String> handler2 =
//                replica2.internal.replicaSystem().acquireHandlerFrom(
//                        replica2.master,
//                        replica2.internal.replicaSystem().acquireHandlerFrom$default$2());
//        WeakAkkaReplicaSystem.WeakSynchronized weakSynchronized =
//                (WeakAkkaReplicaSystem.WeakSynchronized) handler2.request(
//                        replica2.address,
//                        new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(replica2.localOperations),
//                        handler2.request$default$3());
//        Counter result2 = (Counter) weakSynchronized.obj();
//        handler2.close();
//
//        replica2.internal.setObject(result2);
//        replica2.localOperations.clear();
//
//        context2.endTransaction();
//
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + result2.value);
//    }
}
