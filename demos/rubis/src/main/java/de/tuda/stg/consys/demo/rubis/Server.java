package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import java.util.Date;
import java.util.List;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

public class Server extends Thread {
    private int id;
    private int nReplicas;
    private CassandraStoreBinding store;

    Ref<Rubis> rubis;

    public Server(int id, int nReplicas, CassandraStoreBinding store) {
        this.store = store;
        this.id = id;
        this.nReplicas = nReplicas;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    public void init() {
        this.rubis = store.transaction(ctx -> {
            return Option.apply(ctx.lookup("rubis", MIXED, Rubis.class));
        }).get();
    }

    public void run() {
        while (true) {
            store.transaction(ctx -> {
                int nItems = ((List<Ref<Item>>)rubis.ref().getOpenAuctions()).size();
                int batchSize = nItems / nReplicas;
                closeAuctions(id * batchSize, id * batchSize + batchSize);

                return Option.empty();
            });

            try {
                Thread.sleep(10000);
            } catch (InterruptedException e) {}
        }
    }

    @Transactional
    private void closeAuctions(int start, int end) {
        var now = new Date();
        var auctions = (List<Ref<Item>>)rubis.ref().getOpenAuctions();
        for (int i = start; i < end; i++) {
            var auction = auctions.get(i).ref();
            if (now.after(auction.getEndDate())) {
                auction.closeAuction();
                rubis.ref().closeAuction(auction.getName(), auction.getCategory());
            }
        }
    }

    // TODO: auto-bidding
}
