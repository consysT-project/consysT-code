package de.tuda.stg.consys.demo.rubis;

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

public class UserInterface {
    public static ConsistencyLevel<CassandraStore> objectsConsistencyLevel = MIXED;
    private CassandraStoreBinding store;
    private Ref<User> user;
    private Ref<AuctionStore> auctionStore;

    public UserInterface(CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    public void registerUser(String name, String nickname, String password, String email) {
        var userId = UUID.randomUUID();
        this.user = store.transaction(ctx -> {
            var user = ctx.replicate("user:" + nickname, objectsConsistencyLevel, User.class,
                    userId, name, nickname, password, email);

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, objectsConsistencyLevel, AuctionStore.class);
            }
            auctionStore.ref().addUser(user);

            return Option.apply(user);
        }).get();
    }

    public void loginUser(String nickname, String password) {
        var result = store.transaction(ctx -> {
            var user = ctx.lookup("user:" + nickname, objectsConsistencyLevel, User.class);
            if (!(boolean)user.ref().authenticate(password)) {
                throw new AppException("Wrong credentials.");
            }

            if (auctionStore == null) {
                auctionStore = ctx.lookup(Util.auctionStoreKey, objectsConsistencyLevel, AuctionStore.class);
            }

            return Option.apply(user);
        });

        if (result.isDefined()) {
            this.user = result.get();
        }
    }

    public void addBalance(float amount) {
        checkLogin();
        store.transaction(ctx -> {
            user.ref().addBalance(amount);
            return Option.empty();
        });
    }

    public UUID registerItem(String name, String description, Category category, float reservePrice, int durationInSeconds) {
        checkLogin();

        var cal = Calendar.getInstance();
        Date startDate = cal.getTime();
        cal.add(Calendar.SECOND, durationInSeconds);
        Date endDate = cal.getTime();

        float initialPrice = reservePrice * 0.3f;
        float buyNowPrice = reservePrice * 1.3f;

        var itemId = UUID.randomUUID();

        return store.transaction(ctx -> {
            var item = ctx.replicate("item:" + itemId, objectsConsistencyLevel, Item.class,
                    itemId, name, description, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                    category, user);

            user.ref().addOwnAuction(item);
            auctionStore.ref().addItem(item, Category.MISC);

            return Option.apply(itemId);
        }).get();
    }

    public boolean placeBid(UUID itemId, float bidAmount) throws TimeoutException {
        checkLogin();

        var bidId = UUID.randomUUID();
        return store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                throw new AppException("You cannot bid on your own items.");
            }

            if (!Util.hasEnoughCredits(user, bidAmount)) {
                throw new AppException.NotEnoughCreditsException();
            }

            var bid = ctx.replicate("bid:" + bidId, objectsConsistencyLevel, Bid.class,
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
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
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
            List<Ref<Item>> items = auctionStore.ref().browseItems(category);
            sb.append("Items in category '").append(category).append("':\n");
            for (var item : items) {
                sb.append((String)item.ref().toString());
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public void endAuctionImmediately(UUID itemId) throws TimeoutException {
        checkLogin();

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
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

            List<Ref<Item>> watched = user.ref().getOpenBuyerAuctions();
            if (!watched.isEmpty())
                sb.append("Watched items:\n");
            for (var item : watched) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            List<Ref<Item>> open = user.ref().getOpenSellerAuctions();
            if (!open.isEmpty())
                sb.append("Open auctions:\n");
            for (var item : open) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            List<Ref<Item>> bought = user.ref().getBuyerHistory();
            if (!bought.isEmpty())
                sb.append("Bought items:\n");
            for (var item : bought) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            List<Ref<Item>> sold = user.ref().getSellerHistory(true);
            if (!sold.isEmpty())
                sb.append("Sold items:\n");
            for (var item : sold) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            List<Ref<Item>> unsold = user.ref().getSellerHistory(false);
            if (!unsold.isEmpty())
                sb.append("Unsold items:\n");
            for (var item : unsold) {
                sb.append("  ").append((String)item.ref().getName()).append(" (").append(item.ref().getId().toString()).append(")\n");
            }

            return Option.apply(sb.toString());
        }).get();
    }

    public Tuple2<Optional<String>, Float> getTopBid(UUID itemId) {
        return store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
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
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
            return Option.apply(((Date)item.ref().getEndDate()).before(new Date()));
        }).get();
    }

    private void checkLogin() {
        if (user == null) {
            throw new AppException("You must be logged-in in.");
        }
    }
}
