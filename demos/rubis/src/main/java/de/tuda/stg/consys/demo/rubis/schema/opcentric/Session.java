package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;
import scala.Tuple2;

import java.util.*;
import java.util.concurrent.TimeoutException;

@SuppressWarnings({"consistency"})
public class Session {
    private static ConsistencyLevel<CassandraStore> userConsistencyLevel;
    private static ConsistencyLevel<CassandraStore> itemConsistencyLevel;
    private static ConsistencyLevel<CassandraStore> internalConsistencyLevel;
    public static int nMaxRetries;
    public static int retryDelay;

    private Store store;
    private Ref<@Mutable User> user;
    private Random random = new Random();

    public Session(@Mutable Store store) {
        this.store = store;
    }

    private <U> Option<U> doTransaction(TransactionContext transaction,
                                        Function1<TransactionContext, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    private <U> Option<U> doTransactionWithRetries(TransactionContext transaction,
                                        Function1<TransactionContext, Option<U>> code) {
        int nTries = 0;
        while (true) {
            try {
                return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
            } catch (Exception e) {
                if (!(e instanceof TimeoutException)) throw e;
                Logger.warn("Timeout during operation. Retrying...");
                nTries++;
                try { Thread.sleep(random.nextInt(retryDelay)); } catch (InterruptedException ignored) {}
                if (nTries > nMaxRetries) {
                    Logger.err("Timeout during operation. Max retries reached.");
                    throw e;
                }
            }
        }
    }

    public void registerUser(TransactionContext tr,
                             String nickname, String name, String password, String email) {
        @Immutable @Local UUID userId = UUID.randomUUID();
        this.user = doTransaction(tr, ctx -> {
            Ref<@Mutable User> user = ctx.replicate(
                    "user:" + nickname, userConsistencyLevel, User.class,
                    userId, nickname, name, password, email);
            return Option.apply(user);
        }).get();
    }

    public void loginUser(TransactionContext tr,
                          String nickname, String password) {
        @Immutable Option<Ref<@Mutable User>> result = doTransaction(tr, ctx -> {
            Ref<@Mutable User> user = lookupUser(tr, nickname);
            if (!user.ref().authenticate(password)) {
                throw new AppException("Wrong credentials.");
            }
            return Option.apply(user);
        });

        if (result.isDefined()) {
            this.user = result.get();
        }
    }

    public void addBalance(TransactionContext tr, @Strong float amount) {
        checkLogin();
        doTransaction(tr, ctx -> {
            user.ref().addBalance(amount);
            return Option.apply(0);
        });
    }

    public Ref<Item> registerItem(TransactionContext tr,
                             String name, String description, Category category,
                             float reservePrice, int durationInSeconds) {
        @Immutable @Local UUID itemId = UUID.randomUUID();
        return registerItem(tr, itemId.toString(), itemId, name, description, category, reservePrice, durationInSeconds);
    }

    Ref<Item> registerItem(TransactionContext tr,
                           String replId, UUID itemId,
                           String name, String description, Category category,
                           float reservePrice, int durationInSeconds) {
        checkLogin();

        Calendar cal = (@Mutable Calendar) Calendar.getInstance();
        Date startDate = (@Mutable Date) cal.getTime();
        cal.add(Calendar.SECOND, durationInSeconds);
        Date endDate = (@Mutable Date) cal.getTime();

        float initialPrice = reservePrice * 0.3f;
        float buyNowPrice = reservePrice * 1.3f;

        Ref<Item> item = doTransaction(tr, ctx ->
                Option.apply(ctx.replicate(makeItemAddress(replId), itemConsistencyLevel, Item.class,
                        itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                        category, user))
        ).get();

        return doTransaction(tr, cty -> {
            user.ref().addOwnAuction(item);
            return Option.apply(item);
        }).get();
    }

    public boolean placeBid(TransactionContext tr, UUID itemId, float bidAmount) {
        Ref<Item> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        return placeBid(tr, item, bidAmount);
    }

    public boolean placeBid(TransactionContext tr, Ref<Item> item, float bidAmount) {
        checkLogin();

        @Immutable @Local UUID bidId = UUID.randomUUID();
        return doTransactionWithRetries(tr, ctx -> {
            var bid = new Bid(bidId, bidAmount, user);
            boolean reserveMet = item.ref().placeBid(bid);
            user.ref().addWatchedAuction(item);
            return Option.apply(reserveMet);
        }).get();
    }

    public void buyNow(TransactionContext tr, UUID itemId) {
        Ref<Item> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        buyNow(tr, item);
    }

    public void buyNow(TransactionContext tr, Ref<Item> item) {
        checkLogin();

        doTransactionWithRetries(tr, ctx -> {
            item.ref().buyNow(user, item);
            return Option.apply(0);
        });
    }

    public String browseItemsByReplIds(TransactionContext tr, String[] replIds) {
        checkLogin();

        // in MIXED and STRONG cases a deadlock can occur, since stringifying an item accesses strong state
        return doTransactionWithRetries(tr, ctx -> {
            var sb = new StringBuilder();
            @Immutable List<Ref<Item>> items = new ArrayList<>(replIds.length);
            for (String replId : replIds) {
                items.add(lookupItem(tr, replId));
            }

            sb.append("Items:\n");
            for (Ref<Item> item : items) {
                sb.append(item.ref().toString()).append("\n");
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public void endAuctionImmediately(TransactionContext tr, UUID itemId) {
        Ref<Item> item = doTransaction(tr, ctx ->
                Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        endAuctionImmediately(tr, item);
    }

    public void endAuctionImmediately(TransactionContext tr, Ref<Item> item) {
        checkLogin();

        doTransaction(tr, ctx -> {
            if (!item.ref().getSeller().ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You can only end your own auctions.");
            }

            item.ref().setEndDateToNow();
            item.ref().closeAuction(item);

            return Option.apply(0);
        });
    }

    public String printUserInfo(TransactionContext tr, boolean full) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            var sb = new StringBuilder();
            sb.append(user.ref().toString());

            if (!full) {
                return Option.apply(sb.toString());
            }
            sb.append("\n");

            var watched = user.ref().getOpenBuyerAuctions();
            if ((@Weak boolean)!watched.isEmpty())
                sb.append("Watched items:\n");
            for (var item : watched) {
                sb.append("  ").append(item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            var open = user.ref().getOpenSellerAuctions();
            if ((@Weak boolean)!open.isEmpty())
                sb.append("Open auctions:\n");
            for (var item : open) {
                sb.append("  ").append(item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            var bought = user.ref().getBuyerHistory();
            if ((@Weak boolean)!bought.isEmpty())
                sb.append("Bought items:\n");
            for (var item : bought) {
                sb.append("  ").append(item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            var sold = user.ref().getSellerHistory(true);
            if ((@Weak boolean)!sold.isEmpty())
                sb.append("Sold items:\n");
            for (var item : sold) {
                sb.append("  ").append(item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            var unsold = user.ref().getSellerHistory(false);
            if ((@Weak boolean)!unsold.isEmpty())
                sb.append("Unsold items:\n");
            for (var item : unsold) {
                sb.append("  ").append(item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            return Option.apply(sb.toString());
        }).get();
    }

    public Tuple2<Optional<String>, Float> getTopBidAndBidder(TransactionContext tr, UUID itemId) {
        return doTransaction(tr, ctx -> {
            Ref<Item> item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            Optional<Bid> bid = item.ref().getTopBid();
            if (bid.isPresent())
                return Option.apply(new Tuple2<>(
                        Optional.of((bid.get().getUser()).ref().getNickname().toString()),
                        bid.get().getBid()));
            return Option.apply(new Tuple2<>(
                    Optional.<String>empty(),
                    item.ref().getTopBidPrice()));
        }).get();
    }

    public float getBidPrice(TransactionContext tr, Ref<Item> item) {
        return doTransaction(tr, ctx -> Option.<Float>apply(item.ref().getTopBidPrice())).get();
    }

    public boolean hasAuctionEnded(TransactionContext tr, UUID itemId) {
        return doTransaction(tr, ctx -> {
            Ref<Item> item = lookupItem(tr, itemId.toString());
            return Option.apply((item.ref().getEndDate()).before(new Date()));
        }).get();
    }

    public boolean hasAuctionEnded(TransactionContext tr, Ref<Item> item) {
        return doTransaction(tr, ctx ->
            Option.apply((item.ref().getEndDate()).before(new Date()))
        ).get();
    }

    public Ref<@Mutable User> lookupUser(TransactionContext tr, String nickname) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(makeUserAddress(nickname), userConsistencyLevel, User.class))).get();
    }

    Ref<Item> lookupItem(TransactionContext tr, String replId) {
        return doTransaction(tr, ctx ->
                Option.apply(ctx.lookup(makeItemAddress(replId), itemConsistencyLevel, Item.class))
        ).get();
    }

    private String makeUserAddress(String id) {
        return "user:" + id;
    }

    private String makeItemAddress(String id) {
        return "item:" + id;
    }

    private void checkLogin() {
        if (user == null) {
            throw new AppException("You must be logged in.");
        }
    }
}
