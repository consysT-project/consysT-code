package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;
import scala.Option;

import java.util.Date;;
import java.util.List;
import java.util.UUID;

public class Client {
    private CassandraStoreBinding store;
    private Ref<User> user;

    public Client(CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    public void registerUser(String name, String nickname, String password, String email) {
        this.user = store.transaction(ctx -> {
            // TODO: prevent override
            var id = UUID.randomUUID();
            var user = ctx.replicate("user:" + nickname, MIXED, User.class,
                    id, name, nickname, password, email);

            var rubis = ctx.lookup("rubis", MIXED, Rubis.class);
            rubis.ref().addUser(user);

            return Option.apply(user);
        }).get();
    }

    public void loginUser(String nickname, String password) {
        var result = store.transaction(ctx -> {
            var user = ctx.lookup("user:" + nickname, MIXED, User.class);
            if (!(boolean)user.ref().authenticate(password)) {
                System.out.println("wrong password");
                return Option.empty();
            }
            return Option.apply(user);
        });
        if (result.isDefined()) {
            this.user = result.get();
        }
    }

    public String printUserInfo() {
        if (user == null) {
            System.out.println("You must be logged in in order to show user info.");
            return "";
        }

        return store.transaction(ctx -> Option.<String>apply(user.ref().toString())).get();
    }

    public UUID registerItem(String name, float price) {
        if (user == null) {
            System.out.println("You must be logged-in in order to register items.");
        }

        return store.transaction(ctx -> {
            var id = UUID.randomUUID();
            var item = ctx.replicate("item:" + name, MIXED, Item.class,
                    id, name, "", 1, price, price, price, new Date(), new Date(),
                    Category.EVERYTHING_ELSE, user);
            user.ref().addInsertedAuction(item);

            var rubis = ctx.lookup("rubis", MIXED, Rubis.class);
            rubis.ref().addItem(item, Category.EVERYTHING_ELSE);

            return Option.apply(id);
        }).get();
    }

    public void placeBid(String itemName, float price) {
        if (user == null) {
            System.out.println("You must be logged-in in order to place bids.");
        }

        store.transaction(ctx -> {
            var item = ctx.lookup("item:" + itemName, MIXED, Item.class);
            if (((Ref<User>)item.ref().getSeller()).ref().getNickname().equals(user.ref().getNickname())) {
                System.out.println("You cannot bid on your own items");
                return Option.empty();
            }

            var bidId = UUID.randomUUID();
            var bid = ctx.replicate("bid:" + bidId, MIXED, Bid.class, bidId, price, user, -1.0f);
            item.ref().placeBid(bid);
            // TODO add bid to rubis list
            return Option.empty();
        });
    }

    public void browseCategory(String categoryName) {
        Category category;
        try {
            category = Category.valueOf(categoryName);
        } catch (IllegalArgumentException e) {
            System.out.println("unknown category");
            return;
        }

        store.transaction(ctx -> {
            var rubis = ctx.lookup("rubis", MIXED, Rubis.class);
            var items = rubis.ref().browseItems(category);
            System.out.println("Items in category '" + categoryName + "':");
            for (var item : (List<Ref<Item>>)items) {
                System.out.println("  " + item.ref().getName() +
                        " | bidding price: " + item.ref().getBiddingPrice() +
                        " | Buy-Now price: " + item.ref().getBuyNowPrice());
            }
            return Option.empty();
        });
    }
}
