package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.demo.rubis.schema.AuctionStore;
import de.tuda.stg.consys.demo.rubis.schema.Item;
import de.tuda.stg.consys.demo.rubis.schema.Util;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.Tuple3;

import java.util.Date;
import java.util.List;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

public class BackgroundTask implements Runnable {
    private final int id;
    private final int nReplicas;
    private CassandraStoreBinding store;
    private boolean stop;
    private final long sleepMilliseconds;

    private Ref<AuctionStore> auctionStore;

    public BackgroundTask(int id, int nReplicas, long sleepMilliseconds, CassandraStoreBinding store) {
        this.id = id;
        this.nReplicas = nReplicas;
        this.sleepMilliseconds = sleepMilliseconds;
        this.store = store;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    public void init() {
        this.auctionStore = store.transaction(ctx ->
                Option.<Ref<AuctionStore>>apply(ctx.lookup(Util.auctionStoreKey, MIXED, AuctionStore.class))).get();
    }

    @Override
    public void run() {
        while (!stop) {
            Tuple3<List<Ref<Item>>, Integer, Integer> result = store.transaction(ctx -> {
                List<Ref<Item>> items = auctionStore.ref().getOpenAuctions();
                int nItems = items.size();
                int batchSize = 1 + (nItems / nReplicas);
                int startIndex = id * batchSize;
                int endIndex = id * batchSize + batchSize > nItems ? id * batchSize : id * batchSize + batchSize;
                return Option.apply(new Tuple3<>(items, startIndex, endIndex));
            }).get();

            closeAuctions(result._1(), result._2(), result._3());

            try {
                Thread.sleep(sleepMilliseconds);
            } catch (InterruptedException e) {
                return;
            }
        }
    }

    private void closeAuctions(List<Ref<Item>> auctions, int start, int end) {
        for (int i = start; i < end; i++) {
            int finalI = i;
            var now = new Date();
            store.transaction(ctx -> {
                Ref<Item> auction = auctions.get(finalI);
                if (now.after(auction.ref().getEndDate())) {
                    Util.closeAuction(auction, auctionStore);
                }
                return Option.empty();
            });
        }
    }

    public void stopThread() {
        stop = true;
    }
}
