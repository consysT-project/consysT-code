package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import scala.Option;
import scala.Tuple2;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.concurrent.TimeoutException;
import java.util.stream.Collectors;

public class UserInterface {
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> itemConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> bidConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> storeConsistencyLevel = MIXED;
    private CassandraStoreBinding store;
    private Ref<@Mutable User> user;
    private Ref<@Mutable AuctionStore> auctionStore;

    public UserInterface(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    public void registerUser(String nickname, String name, String password, String email) {
        @Immutable @Local UUID userId = UUID.randomUUID();
        this.user = store.transaction(ctx -> {
            Ref<@Mutable User> user = ctx.replicate("user:" + nickname, userConsistencyLevel, User.class,
                    userId, nickname, name, password, email);

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, storeConsistencyLevel, AuctionStore.class);
            }

            return Option.apply(user);
        }).get();
    }

    public void loginUser(String nickname, String password) {
        @Immutable Option<Ref<@Mutable User>> result = store.transaction(ctx -> {
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

    public void addBalance(@Strong float amount) {
        checkLogin();
        store.transaction(ctx -> {
            user.ref().addBalance(amount);
            return Option.empty();
        });
    }

    public UUID registerItem(String name, String description, Category category, float reservePrice, int durationInSeconds) {
        checkLogin();

        Calendar cal = (@Mutable Calendar) Calendar.getInstance();
        Date startDate = (@Mutable Date) cal.getTime();
        cal.add(Calendar.SECOND, durationInSeconds);
        Date endDate = (@Mutable Date) cal.getTime();

        float initialPrice = reservePrice * 0.3f;
        float buyNowPrice = reservePrice * 1.3f;

        @Immutable @Local UUID itemId = UUID.randomUUID();
        return store.transaction(ctx -> {
            var item = ctx.replicate("item:" + itemId, itemConsistencyLevel, Item.class,
                    itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                    category, user);

            user.ref().addOwnAuction(item);
            auctionStore.ref().addItem(item, Category.MISC);

            return Option.apply(itemId);
        }).get();
    }

    public boolean placeBid(UUID itemId, float bidAmount) throws TimeoutException {
        checkLogin();

        @Immutable @Local UUID bidId = UUID.randomUUID();
        return store.transaction(ctx -> {
            Ref<@Mutable Item> item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You cannot bid on your own items.");
            }

            if (!Util.hasEnoughCredits(user, bidAmount)) {
                throw new AppException.NotEnoughCreditsException();
            }

            var bid = ctx.replicate("bid:" + bidId, bidConsistencyLevel, Bid.class,
                    bidId, bidAmount, user);

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

    public void buyNow(UUID itemId) throws TimeoutException {
        checkLogin();

        store.transaction(ctx -> {
            Ref<@Mutable Item> item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You cannot buy your own items.");
            }

            Util.buyItemNow(item, user, auctionStore);
            return Option.empty();
        });
    }

    public String browseCategory(Category category) {
        checkLogin();

        return store.transaction(ctx -> {
            var sb = new StringBuilder();
            @Immutable List<Ref<Item>> items = auctionStore.ref().browseItems(category);
            sb.append("Items in category '").append(category).append("':\n");
            for (var item : items) {
                sb.append((String)item.ref().toString());
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public List<UUID> browseCategoryItems(Category category) {
        checkLogin();

        return store.transaction(ctx -> {
            @Immutable List<Ref<Item>> items = auctionStore.ref().browseItems(category);
            return Option.apply(items.stream().map(item -> (UUID)item.ref().getId()).collect(Collectors.toList()));
        }).get();
    }

    public void endAuctionImmediately(UUID itemId) throws TimeoutException {
        checkLogin();

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            if (!((Ref<User>)item.ref().getSeller()).ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You can only end your own auctions.");
            }

            item.ref().endAuctionNow();
            Util.closeAuction(item, auctionStore);

            return Option.empty();
        });
    }

    public String printUserInfo(boolean full) {
        checkLogin();

        return store.transaction(ctx -> {
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

    public Tuple2<Optional<String>, Float> getTopBid(UUID itemId) {
        return store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            Optional<Ref<Bid>> bid = item.ref().getTopBid();
            if (bid.isPresent())
                return Option.apply(new Tuple2<>(
                        Optional.of(((Ref<User>)bid.get().ref().getUser()).ref().getNickname().toString()),
                        (float)bid.get().ref().getBid()));
            return Option.apply(new Tuple2<>(
                    Optional.<String>empty(),
                    (float)item.ref().getTopBidPrice()));
        }).get();
    }

    public boolean hasAuctionEnded(UUID itemId) {
        return store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, itemConsistencyLevel, Item.class);
            return Option.apply(((Date)item.ref().getEndDate()).before(new Date()));
        }).get();
    }

    private void checkLogin() {
        if (user == null) {
            throw new AppException("You must be logged-in in.");
        }
    }
}
