package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.Tuple2;
import scala.concurrent.duration.Duration;

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.*;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

@SuppressWarnings({"consistency"})
public class TestRunner {
    private static final int msReplicaTimeout = 50;
    private static final int msServerSleep = 1000;
    private static final boolean enableLog = true;
    private static final int nReplicas = 3;
    private static final int nBackgroundTasks = 0;

    private static ExecutorService threadPool;
    private static final List<Future<?>> threadFutures = new LinkedList<>();

    private static final CassandraStoreBinding[] replicas = new CassandraStoreBinding[nReplicas];
    private static final Session[] SESSIONS = new Session[nReplicas];
    private static final BackgroundTask[] backgroundTasks = new BackgroundTask[nBackgroundTasks];
    private static final UUID[] items = new UUID[5];

    public static void main(String[] args) throws InterruptedException {
        threadPool = Executors.newFixedThreadPool(backgroundTasks.length + SESSIONS.length);
        initConnections();
        run();
        closeConnections();
    }

    private static void initConnections() {
        for (int i = 0; i < replicas.length; i++) {
            replicas[i] = Cassandra.newReplica("127.0.0." + (i+1), 9042, 2181,
                    Duration.apply(msReplicaTimeout, "ms"), i == 0);
        }

        replicas[0].transaction(ctx -> {
            ctx.replicate(Util.auctionStoreKey, MIXED, AuctionStore.class);
            return Option.empty();
        });

        for (int i = 0; i < backgroundTasks.length; i++) {
            backgroundTasks[i] = new BackgroundTask(i, backgroundTasks.length, msServerSleep, replicas[i % replicas.length]);
            backgroundTasks[i].init();
        }

        for (int i = 0; i < SESSIONS.length; i++) {
            SESSIONS[i] = new Session(replicas[i % replicas.length]);
        }
    }

    private static void closeConnections() {
        for (var server : backgroundTasks)
            server.stopThread();

        try {
            for (var replica : replicas)
                replica.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }

    public static void run() throws InterruptedException {
        for (var task : backgroundTasks) {
            threadFutures.add(threadPool.submit(task));
        }

        System.out.println("> Starting auctions...");
        Session sellerInterface = SESSIONS[0];
        sellerInterface.registerUser(null, "0", "0", "", "");
        items[0] = sellerInterface.registerItem(null, "item0", "", Category.MISC, 50, 60);
        items[1] = sellerInterface.registerItem(null, "item1", "", Category.MISC, 50, 60);
        items[2] = sellerInterface.registerItem(null, "item2", "", Category.MISC, 50, 60);
        items[3] = sellerInterface.registerItem(null, "item3", "", Category.MISC, 50, 60);
        items[4] = sellerInterface.registerItem(null, "item4", "", Category.MISC, 50, 60);

        System.out.println("> Starting bidding...");
        threadFutures.add(threadPool.submit(new UserTask(1, new UUID[]{items[0], items[1]}, 100, 5)));
        threadFutures.add(threadPool.submit(new UserTask(2, new UUID[]{items[0], items[1], items[2]}, 90, 5)));

        Thread.sleep(10000);

        System.out.println("> Ending auctions...");
        boolean end = false;
        while (!end) {
            try {
                for (var item : items)
                    sellerInterface.endAuctionImmediately(null, item);
                end = true;
            } catch (Exception ignored) {
                if (!(ignored instanceof RuntimeException))
                    throw ignored;
            }
        }

        threadPool.shutdown();

        for (var task : backgroundTasks) {
            task.stopThread();
        }

        for (var future: threadFutures) {
            try {
                future.get();
            } catch (ExecutionException e) {
                e.printStackTrace();
            }
        }

        // all threads are done, all (strong) data is propagated

        System.out.println("--------------");
        for (var client : SESSIONS) {
            System.out.println(client.printUserInfo(null, true));
        }
    }

    static class UserTask implements Runnable {
        private final Session session;
        private final UUID[] watchedItems;
        private final String userName;
        private final float maxBid;
        float bidIncrement;

        UserTask(int id, UUID[] watchedItems, float maxBid, float bidIncrement) {
            session = SESSIONS[id];
            this.watchedItems = watchedItems;
            this.maxBid = maxBid;
            this.bidIncrement = bidIncrement;
            userName = String.valueOf(id);

            session.registerUser(null, userName, "", "", "");
            session.addBalance(null, 1000);
        }

        @Override
        public void run() {
            boolean[] reservesMet = new boolean[watchedItems.length];
            int nCompletedItems = 0;
            while (nCompletedItems < watchedItems.length) {
                for (int i = 0; i < watchedItems.length; i++) {
                    var item = watchedItems[i];
                    Tuple2<Optional<String>, Float> bid = session.getTopBidAndBidder(null, item);
                    float newBid = bid._2 + bidIncrement;

                    if(newBid <= maxBid && (!(bid._1.isPresent() && bid._1.get().equals(userName)) || !reservesMet[i])) {
                        try {
                            reservesMet[i] = session.placeBid(null, item, newBid);
                            if (enableLog) System.out.println("User '" + userName + "' bids " + newBid + " on item " + i +
                                    (reservesMet[i] ? "" : " but reserve not met."));
                        } catch (AppException.DateException ignored) {
                            if (enableLog) System.out.println("User '" + userName + "' bids " + newBid + " on item " + i +
                                    " but auction has already ended.");
                            nCompletedItems++; // auction ended
                        } catch (AppException ignored) {
                            if (enableLog) System.out.println("User '" + userName + "' bids " + newBid + " on item " + i +
                                    " but was outbid during processing.");
                            // we were outbid during processing, try again
                        }
                        catch (Exception ignored) {
                            if (ignored instanceof TimeoutException) {
                                if (enableLog) System.out.println("User '" + userName + "' bids " + newBid + " on item " + i +
                                        " but auction is locked by another user.");
                                // auction is locked, try again
                            } else {
                                throw ignored;
                            }
                        }
                    } else if (newBid > maxBid) {
                        //System.out.println("too expensive");
                        nCompletedItems++;
                    } else if (session.hasAuctionEnded(null, item)) {
                        //System.out.println("ended");
                        nCompletedItems++;
                    }
                }
                try {
                    Thread.sleep(80);
                } catch (InterruptedException e) {
                    return;
                }
            }
        }
    }
}
