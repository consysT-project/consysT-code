package de.tuda.stg.consys.demo.rubis;

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

public class TestRunner {
    private static final int msTimeout = 50;
    private static final int msServerSleep = 1000;

    private static ExecutorService threadPool;
    private static final List<Future<?>> threadFutures = new LinkedList<>();

    private static final CassandraStoreBinding[] replicas = new CassandraStoreBinding[3];
    private static final Client[] clients = new Client[3];
    private static final Server[] servers = new Server[3];
    private static final UUID[] items = new UUID[5];

    public static void main(String[] args) throws InterruptedException {
        threadPool = Executors.newFixedThreadPool(servers.length + clients.length);
        initConnections();
        run();
        closeConnections();
    }

    private static void initConnections() {
        replicas[0] = Cassandra.newReplica("127.0.0.1", 9042, 2181,
                Duration.apply(msTimeout, "ms"), true);
        replicas[1] = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                Duration.apply(msTimeout, "ms"), false);
        replicas[2] = Cassandra.newReplica("127.0.0.3", 9042, 2181,
                Duration.apply(msTimeout, "ms"), false);

        replicas[0].transaction(ctx -> {
            ctx.replicate("rubis", MIXED, AuctionStore.class);
            return Option.empty();
        });

        servers[0] = new Server(0, 3, msServerSleep, replicas[0]);
        servers[1] = new Server(1, 3, msServerSleep, replicas[1]);
        servers[2] = new Server(2, 3, msServerSleep, replicas[2]);

        servers[0].init();
        servers[1].init();
        servers[2].init();

        clients[0] = new Client(replicas[0]);
        clients[1] = new Client(replicas[1]);
        clients[2] = new Client(replicas[2]);
    }

    private static void closeConnections() {
        for (var server : servers)
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
        for (var server : servers) {
            //threadFutures.add(threadPool.submit(server));
        }

        Client sellerClient = clients[0];

        System.out.println("> Starting auctions...");
        sellerClient.registerUser("", "0", "", "");
        items[0] = sellerClient.registerItem("item0", "", Category.MISC, 50, 60);
        items[1] = sellerClient.registerItem("item1", "", Category.MISC, 50, 60);
        items[2] = sellerClient.registerItem("item2", "", Category.MISC, 50, 60);
        items[3] = sellerClient.registerItem("item3", "", Category.MISC, 50, 60);
        items[4] = sellerClient.registerItem("item4", "", Category.MISC, 50, 60);

        System.out.println("> Starting bidding...");
        threadFutures.add(threadPool.submit(new Test(1, new UUID[]{items[0], items[1]}, 100)));
        threadFutures.add(threadPool.submit(new Test(2, new UUID[]{items[0], items[1], items[2]}, 90)));

        Thread.sleep(10000);

        System.out.println("> Ending auctions...");
        try {
            for (var item : items) {
                sellerClient.endAuctionImmediately(item);
            }
        } catch (TimeoutException e) {
            System.out.println(e.getMessage());
        }

        threadPool.shutdown();

        for (var server : servers) {
            //server.stopThread();
        }

        for (var future: threadFutures) {
            try {
                future.get();
            } catch (ExecutionException e) {
                e.printStackTrace();
            }
        }

        System.out.println("--------------");
        System.out.println(clients[0].printUserInfo(true));
        System.out.println(clients[1].printUserInfo(true));
        System.out.println(clients[2].printUserInfo(true));
    }

    static class Test implements Runnable {
        private final Client client;
        private final UUID[] watchedItems;
        private final String userName;
        private final float maxBid;

        Test(int id, UUID[] watchedItems, float maxBid) {
            client = clients[id];
            this.watchedItems = watchedItems;
            this.maxBid = maxBid;
            userName = String.valueOf(id);

            client.registerUser("", userName, "", "");
            client.addBalance(1000);
        }

        @Override
        public void run() {
            float increment = 3;

            int i = 0;
            while (i < watchedItems.length) {
                for (var item : watchedItems) {
                    Tuple2<Optional<String>, Float> bid = client.getTopBid(item);
                    if(bid._2 + increment <= maxBid && !(bid._1.isPresent() && bid._1.get().equals(userName))) {
                        //System.out.println(userName + " " + item + " " + bid._2 + " " +
                        // (bid._2 + increment) + " " + (bid._1.isPresent() ? bid._1.get() : ""));
                        try {
                            boolean reserveMet = client.placeBid(item, bid._2 + increment);
                            // TODO: retry if reserve not met
                        } catch (DateException ignored) {
                            //System.out.println("ended");
                            i++; // auction ended
                        } catch (AppException ignored) {
                            //System.out.println("outbid"); // we were outbid during processing, try again
                        } catch (TimeoutException ignored) {
                            //System.out.println("locked"); // auction is locked, try again
                        }
                    } else if (bid._2 + increment > maxBid) {
                        //System.out.println("too expensive");
                        i++;
                    } else if (client.hasAuctionEnded(item)) {
                        //System.out.println("ended");
                        i++;
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
