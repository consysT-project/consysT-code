package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;
import scala.Tuple2;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.concurrent.TimeoutException;

@SuppressWarnings({"consistency"})
public class Session {
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> itemConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> storeConsistencyLevel = MIXED;
    private CassandraStoreBinding store;
    private Ref<@Mutable User> user;
    private Ref<@Mutable AuctionStore> auctionStore;

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    private <U> Option<U> doTransaction(CassandraTransactionContextBinding transaction,
                                        Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    public void registerUser(CassandraTransactionContextBinding tr,
                             String nickname, String name, String password, String email) {
        @Immutable @Local UUID userId = UUID.randomUUID();
        this.user = doTransaction(tr, ctx -> {
            Ref<@Mutable User> user = ctx.replicate("user:" + nickname, userConsistencyLevel, User.class,
                    userId, nickname, name, password, email);

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, storeConsistencyLevel, AuctionStore.class);
            }

            return Option.apply(user);
        }).get();
    }

    public void loginUser(CassandraTransactionContextBinding tr,
                          String nickname, String password) {
        @Immutable Option<Ref<@Mutable User>> result = doTransaction(tr, ctx -> {
            var user = ctx.lookup("user:" + nickname, userConsistencyLevel, User.class);
            if (!(boolean)user.ref().authenticate(password)) {
                throw new AppException("Wrong credentials.");
            }

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, storeConsistencyLevel, AuctionStore.class);
            }

            return Option.apply(user);
        });

        if (result.isDefined()) {
            this.user = result.get();
        }
    }

    public void addBalance(CassandraTransactionContextBinding tr,
                           @Strong float amount) {
        checkLogin();
        doTransaction(tr, ctx -> {
            user.ref().addBalance(amount);
            return Option.empty();
        });
    }

    public UUID registerItem(CassandraTransactionContextBinding tr,
                             String name, String description, Category category, float reservePrice, int durationInSeconds) {
        checkLogin();

        Calendar cal = (@Mutable Calendar) Calendar.getInstance();
        Date startDate = (@Mutable Date) cal.getTime();
        cal.add(Calendar.SECOND, durationInSeconds);
        Date endDate = (@Mutable Date) cal.getTime();

        float initialPrice = reservePrice * 0.3f;
        float buyNowPrice = reservePrice * 1.3f;

        @Immutable @Local UUID itemId = UUID.randomUUID();
        return doTransaction(tr, ctx -> {
            var item = ctx.replicate("item:" + itemId, itemConsistencyLevel, Item.class,
                    itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                    category, user);

            user.ref().addOwnAuction(item);
            auctionStore.ref().addItem(item, Category.MISC);

            return Option.apply(itemId);
        }).get();
    }

    public boolean placeBid(CassandraTransactionContextBinding tr,
                            UUID itemId, float bidAmount) {
        Ref<Item> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        return placeBid(tr, item, bidAmount);
    }

    public boolean placeBid(CassandraTransactionContextBinding tr,
                             Ref<Item> item, float bidAmount) {
        checkLogin();

        @Immutable @Local UUID bidId = UUID.randomUUID();
        return doTransaction(tr, ctx -> {
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You cannot bid on your own items.");
            }

            if (!Util.hasEnoughCredits(user, bidAmount)) {
                throw new AppException.NotEnoughCreditsException();
            }

            var bid = new Bid(bidId, bidAmount, user);

            try {
                boolean reserveMet = item.ref().placeBid(bid);
                user.ref().addWatchedAuction(item);
                return Option.apply(reserveMet);
            } catch (Exception e) {
                if (e instanceof InvocationTargetException &&
                        ((InvocationTargetException)e).getCause() instanceof RuntimeException) {
                    throw (RuntimeException) e.getCause();
                } else {
                    throw e;
                }
            }
        }).get();
    }

    public void buyNow(CassandraTransactionContextBinding tr,
                       UUID itemId) {
        Ref<Item> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        buyNow(tr, item);
    }

    public void buyNow(CassandraTransactionContextBinding tr, Ref<Item> item) {
        checkLogin();

        doTransaction(tr, ctx -> {
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You cannot buy your own items.");
            }

            Util.buyItemNow(item, user, auctionStore);
            return Option.empty();
        });
    }

    public String browseCategory(CassandraTransactionContextBinding tr, Category category, int count) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            var sb = new StringBuilder();
            @Immutable List<Ref<Item>> items = auctionStore.ref().browseItems(category);
            sb.append("Items in category '").append(category).append("':\n");
            for (int i = 0; i < Math.min(items.size(), count); i++) {
                sb.append((String)items.get(i).ref().toString());
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public List<Ref<Item>> browseCategoryItems(CassandraTransactionContextBinding tr, Category category) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            @Immutable List<Ref<Item>> items = auctionStore.ref().browseItems(category);
            return Option.apply(items);
        }).get();
    }

    public void endAuctionImmediately(CassandraTransactionContextBinding tr,
                                      UUID itemId) {
        Ref<Item> item = doTransaction(tr, ctx ->
                Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class))).get();
        endAuctionImmediately(tr, item);
    }

    public void endAuctionImmediately(CassandraTransactionContextBinding tr,
                                      Ref<Item> item) {
        checkLogin();

        doTransaction(tr, ctx -> {
            if (!((Ref<User>)item.ref().getSeller()).ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You can only end your own auctions.");
            }

            item.ref().endAuctionNow();
            Util.closeAuction(item, auctionStore);

            return Option.empty();
        });
    }

    public String printUserInfo(CassandraTransactionContextBinding tr,
                                boolean full) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            var sb = new StringBuilder();
            sb.append((String)user.ref().toString());

            if (!full) {
                return Option.apply(sb.toString());
            }
            sb.append("\n");

            @Immutable @Weak List<Ref<Item>> watched = user.ref().getOpenBuyerAuctions();
            if ((@Weak boolean)!watched.isEmpty())
                sb.append("Watched items:\n");
            for (var item : watched) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            @Immutable @Weak List<Ref<Item>> open = user.ref().getOpenSellerAuctions();
            if ((@Weak boolean)!open.isEmpty())
                sb.append("Open auctions:\n");
            for (var item : open) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            @Immutable @Weak List<Ref<Item>> bought = user.ref().getBuyerHistory();
            if ((@Weak boolean)!bought.isEmpty())
                sb.append("Bought items:\n");
            for (var item : bought) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            @Immutable @Weak List<Ref<Item>> sold = user.ref().getSellerHistory(true);
            if ((@Weak boolean)!sold.isEmpty())
                sb.append("Sold items:\n");
            for (var item : sold) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            @Immutable @Weak List<Ref<Item>> unsold = user.ref().getSellerHistory(false);
            if ((@Weak boolean)!unsold.isEmpty())
                sb.append("Unsold items:\n");
            for (var item : unsold) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            return Option.apply(sb.toString());
        }).get();
    }

    public Tuple2<Optional<String>, Float> getTopBidAndBidder(CassandraTransactionContextBinding tr,
                                                              UUID itemId) {
        return doTransaction(tr, ctx -> {
            var item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            Optional<Bid> bid = item.ref().getTopBid();
            if (bid.isPresent())
                return Option.apply(new Tuple2<>(
                        Optional.of(((Ref<User>)bid.get().getUser()).ref().getNickname().toString()),
                        (float)bid.get().getBid()));
            return Option.apply(new Tuple2<>(
                    Optional.<String>empty(),
                    (float)item.ref().getTopBidPrice()));
        }).get();
    }

    public float getBidPrice(CassandraTransactionContextBinding tr,
                             Ref<Item> item) {
        return doTransaction(tr, ctx -> Option.<Float>apply(item.ref().getTopBidPrice())).get();
    }

    public boolean hasAuctionEnded(CassandraTransactionContextBinding tr,
                                   UUID itemId) {
        return doTransaction(tr, ctx -> {
            var item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            return Option.apply(((Date)item.ref().getEndDate()).before(new Date()));
        }).get();
    }
    public boolean hasAuctionEnded(CassandraTransactionContextBinding tr,
                                   Ref<Item> item) {
        return doTransaction(tr, ctx -> {
            return Option.apply(((Date)item.ref().getEndDate()).before(new Date()));
        }).get();
    }

    Ref<Item> getItem(CassandraTransactionContextBinding tr,
                      UUID itemId) {
        return doTransaction(tr, ctx -> {
            return Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class));
        }).get();
    }

    private void checkLogin() {
        if (user == null) {
            throw new AppException("You must be logged in.");
        }
    }
}
