package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;
import scala.Option;

import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.UUID;

public class Client {
    public static ConsistencyLevel<CassandraStore> objectsConsistencyLevel = MIXED;
    private CassandraStoreBinding store;
    private Ref<User> user;
    private Ref<Rubis> rubis;

    public Client(CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    public void registerUser(String name, String nickname, String password, String email) {
        this.user = store.transaction(ctx -> {
            var id = UUID.randomUUID();
            var user = ctx.replicate("user:" + nickname, objectsConsistencyLevel, User.class,
                    id, name, nickname, password, email);

            if (rubis == null) {
                rubis = ctx.lookup("rubis", objectsConsistencyLevel, Rubis.class);
            }
            rubis.ref().addUser(user);

            return Option.apply(user);
        }).get();
    }

    public void loginUser(String nickname, String password) {
        var result = store.transaction(ctx -> {
            var user = ctx.lookup("user:" + nickname, objectsConsistencyLevel, User.class);
            if (!(boolean)user.ref().authenticate(password)) {
                throw new IllegalArgumentException("wrong password");
            }

            if (rubis == null) {
                rubis = ctx.lookup("rubis", objectsConsistencyLevel, Rubis.class);
            }

            return Option.apply(user);
        });

        if (result.isDefined()) {
            this.user = result.get();
        }
    }

    public String printUserInfo(boolean full) {
        checkLogin();
        if (!full) {
            return store.transaction(ctx -> Option.<String>apply(user.ref().toString())).get();
        } else {
            store.transaction(ctx -> {
                List<Ref<Item>> bought = user.ref().getBuyerHistory();
                System.out.println("Bought items:");
                for (var item : bought) {
                    System.out.println("  " + item.ref().getName() + " (" + item.ref().getId());
                }

                List<Ref<Item>> sold = user.ref().getSellerHistory();
                System.out.println("Sold items:");
                for (var item : sold) {
                    System.out.println("  " + item.ref().getName() + " (" + item.ref().getId());
                }

                return Option.empty();
            });
        }
        return "";
    }

    public void addBalance(float amount) {
        checkLogin();
        store.transaction(ctx -> {
            user.ref().addBalance(amount);
            return Option.empty();
        });
    }

    public UUID registerItem(String name, Category category, float reservePrice, int durationInSeconds) {
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
                    itemId, name, "", 1, reservePrice, initialPrice, buyNowPrice, startDate, endDate,
                    category, user);

            user.ref().addInsertedAuction(item);
            rubis.ref().addItem(item, Category.MISC);

            return Option.apply(itemId);
        }).get();
    }

    public void placeBid(UUID itemId, float price) {
        checkLogin();

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                System.out.println("You cannot bid on your own items");
                return Option.empty();
            }

            var bidId = UUID.randomUUID();
            var bid = ctx.replicate("bid:" + bidId, objectsConsistencyLevel, Bid.class,
                    bidId, price, user, -1.0f);
            item.ref().placeBid(bid);
            // TODO add bid to rubis list
            return Option.empty();
        });
    }

    public void buyNow(UUID itemId) {
        checkLogin();

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
            Ref<User> seller = item.ref().getSeller();
            if (seller.ref().getNickname().equals(user.ref().getNickname())) {
                System.out.println("You cannot buy your own items");
                return Option.empty();
            }

            Util.buyItemNow(item, user, rubis);

            return Option.empty();
        });
    }

    public void browseCategory(Category category) {
        checkLogin();

        store.transaction(ctx -> {
            List<Ref<Item>> items = rubis.ref().browseItems(category);
            System.out.println("Items in category '" + category + "':");
            for (var item : items) {
                System.out.println("  " + item.ref().getName() + " (" + item.ref().getId() + ")" +
                        " | bidding price: " + item.ref().getBiddingPrice() +
                        " | Buy-Now price: " + item.ref().getBuyNowPrice() +
                        " | until: " + item.ref().getEndDate());
            }
            return Option.empty();
        });
    }

    public void endAuctionImmediately(UUID itemId) {
        checkLogin();

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemId, objectsConsistencyLevel, Item.class);
            item.ref().endAuctionNow();
            Util.closeAuction(item, rubis);
            return Option.empty();
        });
    }

    private void checkLogin() {
        if (user == null) {
            System.out.println("You must be logged-in in.");
        }
    }
}
