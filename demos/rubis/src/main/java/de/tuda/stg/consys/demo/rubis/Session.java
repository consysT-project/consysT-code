package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.demo.rubis.schema.datacentric.Item;
import de.tuda.stg.consys.demo.rubis.schema.datacentric.NumberBox;
import de.tuda.stg.consys.demo.rubis.schema.datacentric.RefList;
import de.tuda.stg.consys.demo.rubis.schema.datacentric.RefMap;
import de.tuda.stg.consys.japi.Ref;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import scala.Function1;
import scala.Option;
import scala.Tuple2;

import java.io.ByteArrayOutputStream;
import java.io.ObjectOutputStream;
import java.util.*;

@SuppressWarnings({"consistency"})
public class Session {
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> itemConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> storeConsistencyLevel = MIXED;
    public static Class<? extends IItem> itemImpl;
    public static Class<? extends IUser> userImpl;

    public static boolean dataCentric;

    private Store store;
    private Ref<? extends @Mutable IUser> user;
    private Ref<? extends @Mutable AuctionStore> auctionStore;

    public Session(@Mutable Store store) {
        this.store = store;
    }

    public void setStore(@Mutable Store store) {
        this.store = store;
    }

    private <U> Option<U> doTransaction(TransactionContext transaction,
                                        Function1<TransactionContext, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    public void registerUser(TransactionContext tr,
                             String nickname, String name, String password, String email) {
        @Immutable @Local UUID userId = UUID.randomUUID();
        this.user = doTransaction(tr, ctx -> {
            Ref<? extends @Mutable IUser> user;
            if (dataCentric) {
                Ref<@Strong @Mutable NumberBox<@Mutable @Strong Float>> balance =
                        ctx.replicate("user:" + nickname + ":bal", STRONG, (Class<NumberBox<Float>>)(Class)NumberBox.class, 0);
                Ref<@Strong @Mutable RefMap<UUID, Ref<Item>>> buyerAuctions =
                        ctx.replicate("user:" + nickname + ":ba", STRONG, (Class<RefMap<UUID, Ref<Item>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<Item>>> buyerHistory =
                        ctx.replicate("user:" + nickname + ":bh", STRONG, (Class<RefMap<UUID, Ref<Item>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<Item>>> sellerAuctions =
                        ctx.replicate("user:" + nickname + ":sa", STRONG, (Class<RefMap<UUID, Ref<Item>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<Item>>> sellerHistory =
                        ctx.replicate("user:" + nickname + ":sh", STRONG, (Class<RefMap<UUID, Ref<Item>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<Item>>> sellerFailedHistory =
                        ctx.replicate("user:" + nickname + ":sfh", STRONG, (Class<RefMap<UUID, Ref<Item>>>)(Class)RefMap.class);

                user = ctx.replicate("user:" + nickname, userConsistencyLevel, userImpl,
                        userId, nickname, name, password, email,
                        balance, buyerAuctions, buyerHistory, sellerAuctions, sellerHistory, sellerFailedHistory);
            } else {
                user = ctx.replicate("user:" + nickname, userConsistencyLevel, userImpl,
                        userId, nickname, name, password, email);
            }

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, storeConsistencyLevel, AuctionStore.class);
            }

            return Option.apply(user);
        }).get();
    }

    public void loginUser(TransactionContext tr,
                          String nickname, String password) {
        @Immutable Option<Ref<? extends @Mutable IUser>> result = doTransaction(tr, ctx -> {
            Ref<? extends @Mutable IUser> user = ctx.lookup("user:" + nickname, userConsistencyLevel, userImpl);

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

    public Ref<? extends @Mutable IUser> findUser(TransactionContext tr,
                         String nickname) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup("user:" + nickname, userConsistencyLevel, userImpl))).get();
    }

    public void addBalance(TransactionContext tr,
                           @Strong float amount) {
        checkLogin();
        doTransaction(tr, ctx -> {
            user.ref().addBalance(amount);
            return Option.apply(0);
        });
    }

    public UUID registerItem(TransactionContext tr,
                             String name, String description, Category category,
                             float reservePrice, int durationInSeconds) {
        checkLogin();

        Calendar cal = (@Mutable Calendar) Calendar.getInstance();
        Date startDate = (@Mutable Date) cal.getTime();
        cal.add(Calendar.SECOND, durationInSeconds);
        Date endDate = (@Mutable Date) cal.getTime();

        float initialPrice = reservePrice * 0.3f;
        float buyNowPrice = reservePrice * 1.3f;

        @Immutable @Local UUID itemId = UUID.randomUUID();
        Ref<? extends IItem> item = doTransaction(tr, ctx -> {
            if (dataCentric) {
                Ref<@Strong @Mutable Date> endDateRef =
                        ctx.replicate("item:" + itemId + ":ed", STRONG, Date.class, endDate.getTime()); // TODO: replace STRONG with generic
                Ref<@Strong @Mutable RefList<Bid>> bids =
                        ctx.replicate("item:" + itemId + ":bids", STRONG, (Class<RefList<Bid>>)(Class)RefList.class); // TODO: replace STRONG with generic

                return Option.apply(ctx.replicate("item:" + itemId, itemConsistencyLevel, itemImpl,
                        itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDateRef,
                        category, user, auctionStore, bids));
            } else {
                return Option.apply(ctx.replicate("item:" + itemId, itemConsistencyLevel, itemImpl,
                        itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                        category, user, auctionStore));
            }
        }).get();

        doTransaction(tr, cty -> {
            user.ref().addOwnAuction(item);
            return Option.apply(0);
        });

        return doTransaction(tr, ctx -> {
            auctionStore.ref().addItem(item, category);
            return Option.apply(itemId);
        }).get();
    }

    public boolean placeBid(TransactionContext tr,
                            UUID itemId, float bidAmount) {
        Ref<? extends IItem> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl))).get();
        return placeBid(tr, item, bidAmount);
    }

    public boolean placeBid(TransactionContext tr,
                             Ref<? extends IItem> item, float bidAmount) {
        checkLogin();

        @Immutable @Local UUID bidId = UUID.randomUUID();
        return doTransaction(tr, ctx -> {
            var bid = new Bid(bidId, bidAmount, user);
            boolean reserveMet = item.ref().placeBid(bid);
            user.ref().addWatchedAuction(item);
            return Option.apply(reserveMet);
        }).get();
    }

    public void buyNow(TransactionContext tr,
                       UUID itemId) {
        Ref<? extends IItem> item = doTransaction(tr, ctx ->
            Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl))).get();
        buyNow(tr, item);
    }

    public void buyNow(TransactionContext tr, Ref<? extends IItem> item) {
        checkLogin();

        doTransaction(tr, ctx -> {
            item.ref().buyNow(user, item);
            return Option.apply(0);
        });
    }

    public String browseCategory(TransactionContext tr, Category category, int count) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            var sb = new StringBuilder();
            @Immutable List<Ref<? extends IItem>> items = auctionStore.ref().browseItems(category);
            sb.append("Items in category '").append(category).append("':\n");
            for (int i = 0; i < Math.min(items.size(), count); i++) {
                sb.append(items.get(i).ref().toString());
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public List<Ref<? extends IItem>> browseCategoryItems(TransactionContext tr, Category category) {
        checkLogin();

        return doTransaction(tr, ctx -> {
            @Immutable List<Ref<? extends IItem>> items = auctionStore.ref().browseItems(category);
            return Option.apply(items);
        }).get();
    }

    public void endAuctionImmediately(TransactionContext tr,
                                      UUID itemId) {
        Ref<? extends IItem> item = doTransaction(tr, ctx ->
                Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl))).get();
        endAuctionImmediately(tr, item);
    }

    public void endAuctionImmediately(TransactionContext tr,
                                      Ref<? extends IItem> item) {
        checkLogin();

        doTransaction(tr, ctx -> {
            if (!item.ref().getSeller().ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You can only end your own auctions.");
            }

            item.ref().endAuctionNow();
            item.ref().closeAuction(item);

            return Option.apply(0);
        });
    }

    public String printUserInfo(TransactionContext tr,
                                boolean full) {
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

    public Tuple2<Optional<String>, Float> getTopBidAndBidder(TransactionContext tr,
                                                              UUID itemId) {
        return doTransaction(tr, ctx -> {
            Ref<? extends IItem> item = ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl);
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

    public float getBidPrice(TransactionContext tr,
                             Ref<? extends IItem> item) {
        return doTransaction(tr, ctx -> Option.<Float>apply(item.ref().getTopBidPrice())).get();
    }

    public boolean hasAuctionEnded(TransactionContext tr,
                                   UUID itemId) {
        return doTransaction(tr, ctx -> {
            Ref<? extends IItem> item = ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl);
            return Option.apply((item.ref().getEndDate()).before(new Date()));
        }).get();
    }
    public boolean hasAuctionEnded(TransactionContext tr,
                                   Ref<? extends IItem> item) {
        return doTransaction(tr, ctx ->
            Option.apply((item.ref().getEndDate()).before(new Date()))
        ).get();
    }

    Ref<? extends IItem> getItem(TransactionContext tr,
                                 UUID itemId) {
        return doTransaction(tr, ctx ->
                Option.apply(ctx.lookup("item:" + itemId, itemConsistencyLevel, itemImpl))
        ).get();
    }

    private void checkLogin() {
        if (user == null) {
            throw new AppException("You must be logged in.");
        }
    }

    public Ref<? extends IUser> getLoggedInUser() {
        return user;
    }
}
