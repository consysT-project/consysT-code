//package de.tudarmstadt.consistency.concert;
//
//import de.tudarmstadt.consistency.checker.qual.Strong;
//import de.tudarmstadt.consistency.checker.qual.Weak;
//import de.tudarmstadt.consistency.replobj.ConsistencyLevel;
//import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem;
//import de.tudarmstadt.consistency.replobj.actors.ContextPath;
//import de.tudarmstadt.consistency.replobj.actors.Requests;
//import de.tudarmstadt.consistency.replobj.actors.WeakAkkaReplicaSystem;
//import de.tudarmstadt.consistency.replobj.japi.JRef;
//import scala.collection.Seq$;
//import scala.collection.immutable.Nil$;
//
//import java.io.Serializable;
//import java.util.Date;
//
//public class ConcertStrongManual implements Serializable {
//    public Date date;
//    public JRef<@Weak ConcertHall> hall;
//    public JRef<@Weak Band> band;
//    public JRef<@Weak Counter> soldTickets;
//
//    public @Weak int getSoldTickets () {
//        ReplicatedObject<@Strong Counter> soldTicketsReplica = ReplicatedObject.from(soldTickets);
//
//        Counter result = null;
//
//        if (soldTicketsReplica.isFollower) {
//            AkkaReplicaSystem.GlobalContext$ context = soldTicketsReplica.internal.replicaSystem().GlobalContext();
//
//            boolean needNewTx = !context.hasCurrentTransaction();
//
//            if (needNewTx) context.startNewTransaction();
//
//            Requests.RequestHandler<String> handler =
//                    soldTicketsReplica.internal.replicaSystem().acquireHandlerFrom(
//                            soldTicketsReplica.master,
//                            soldTicketsReplica.internal.replicaSystem().acquireHandlerFrom$default$2());
//            WeakAkkaReplicaSystem.WeakSynchronized weakSynchronized =
//                    (WeakAkkaReplicaSystem.WeakSynchronized) handler.request(
//                            soldTicketsReplica.address,
//                            new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(soldTicketsReplica.localOperations),
//                            handler.request$default$3());
//            result = (Counter) weakSynchronized.obj();
//            handler.close();
//
//            soldTicketsReplica.internal.setObject(result);
//            soldTicketsReplica.localOperations.clear();
//
//            if (needNewTx) context.endTransaction();
//        }
//        else if (soldTicketsReplica.isMaster) {
//            result = soldTicketsReplica.internal.getObject();
//        }
//
//        return result.value;
//    }
//
//    public Ticket buyTicket() {
//        ReplicatedObject<@Strong ConcertHall> hallReplica = ReplicatedObject.from(hall);
//
//        ConcertHall result = null;
//
//        if (hallReplica.isFollower) {
//            AkkaReplicaSystem.GlobalContext$ context = hallReplica.internal.replicaSystem().GlobalContext();
//
//            boolean needNewTx = !context.hasCurrentTransaction();
//
//            if (needNewTx) context.startNewTransaction();
//
//            Requests.RequestHandler<String> handler =
//                    hallReplica.internal.replicaSystem().acquireHandlerFrom(
//                            hallReplica.master,
//                            hallReplica.internal.replicaSystem().acquireHandlerFrom$default$2());
//            WeakAkkaReplicaSystem.WeakSynchronized weakSynchronized =
//                    (WeakAkkaReplicaSystem.WeakSynchronized) handler.request(
//                            hallReplica.address,
//                            new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(hallReplica.localOperations),
//                            handler.request$default$3());
//            result = (ConcertHall) weakSynchronized.obj();
//            handler.close();
//
//            hallReplica.internal.setObject(result);
//            hallReplica.localOperations.clear();
//
//            if (needNewTx) context.endTransaction();
//        }
//        else if (hallReplica.isMaster) {
//            result = hallReplica.internal.getObject();
//        }
//
//        if (result.maxAudience > getSoldTickets()) {
//            ReplicatedObject<@Weak Counter> soldTicketsReplica = ReplicatedObject.from(soldTickets);
//
//            if (soldTicketsReplica.isFollower) {
//                AkkaReplicaSystem.GlobalContext$ context = soldTicketsReplica.internal.replicaSystem().GlobalContext();
//
//                boolean needNewTx = !context.hasCurrentTransaction();
//
//                if (needNewTx) context.startNewTransaction();
//
//                ContextPath path = context.getBuilder().nextPath(ConsistencyLevel.Weak$.MODULE$);
//
//                soldTicketsReplica.localOperations.append(Nil$.MODULE$.$colon$colon(
//                        new Requests.InvokeOp(path, "inc", Seq$.MODULE$.empty())));
//
//                Requests.RequestHandler<String> handler =
//                        soldTicketsReplica.internal.replicaSystem().acquireHandlerFrom(
//                                soldTicketsReplica.master,
//                                soldTicketsReplica.internal.replicaSystem().acquireHandlerFrom$default$2());
//                handler.request(
//                        soldTicketsReplica.address,
//                        new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(soldTicketsReplica.localOperations),
//                        handler.request$default$3());
//                handler.close();
//
//                soldTicketsReplica.localOperations.clear();
//
//                if (needNewTx) context.endTransaction();
//            }
//            else if (soldTicketsReplica.isMaster) {
//                soldTicketsReplica.internal.getObject().inc();
//            }
//
//            return new Ticket();
//        }
//        else {
//            return null;
//        }
//    }
//
//    public ConcertStrongManual(Date date, JRef<@Weak ConcertHall> hall, JRef<@Weak Band> band, JRef<@Weak Counter> soldTickets) {
//        this.date = date;
//        this.hall = hall;
//        this.band = band;
//        this.soldTickets = soldTickets;
//    }
//}
