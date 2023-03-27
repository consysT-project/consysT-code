package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.rubis.schema.AppException;
import de.tuda.stg.consys.demo.rubis.schema.ISession;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;

import java.io.Serializable;
import java.util.*;
import java.util.concurrent.TimeoutException;

@SuppressWarnings({"consistency"})
public class Session<SStore extends de.tuda.stg.consys.core.store.Store> extends ISession<SStore> {
    private final Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>> store;
    private final ConsistencyLevel<SStore> userConsistencyLevel;
    private final ConsistencyLevel<SStore> itemConsistencyLevel;
    private Ref<User> user;
    private String userId;
    private final Random random = new Random();

    public Session(Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>> store,
                   ConsistencyLevel<SStore> userConsistencyLevel,
                   ConsistencyLevel<SStore> itemConsistencyLevel) {
        this.store = store;
        this.userConsistencyLevel = userConsistencyLevel;
        this.itemConsistencyLevel = itemConsistencyLevel;
    }

    private <U> Option<U> doTransaction(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> transaction,
            Function1<TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    private <U> Option<U> doTransactionWithRetries(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> transaction,
            Function1<TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Option<U>> code) {
        int nTries = 0;
        while (true) {
            try {
                return doTransaction(transaction, code);
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

    public String registerUser(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
                             String userId, String nickname, String name, String password, String email) {
        this.user = doTransaction(tr, ctx -> {
            Ref<@Mutable User> user = ctx.replicate(
                    makeUserAddress(userId), userConsistencyLevel, User.class,
                    UUID.randomUUID(), nickname, name, password, email);
            return Option.apply(user);
        }).get();
        this.userId = userId;

        return userId;
    }

    public String registerItem(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
                           String itemId, String name, String description, Category category,
                           float reservePrice, int durationInSeconds) {
        checkLogin();

        Ref<Item> item = doTransaction(tr, ctx ->
                Option.apply(ctx.replicate(makeItemAddress(itemId), itemConsistencyLevel, Item.class,
                        UUID.randomUUID(), name, description,
                        reservePrice, getInitialPrice(reservePrice), getBuyNowPrice(reservePrice),
                        new Date(), getEndDateFromDuration(durationInSeconds), category, user))
        ).get();

        doTransaction(tr, cty -> {
            user.ref().addOwnAuction(item);
            return Option.apply(0);
        });

        return itemId;
    }

    public void addBalance(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, float amount) {
        checkLogin();

        doTransaction(tr, ctx -> {
            user.ref().addBalance(amount);
            return Option.apply(0);
        });
    }

    @Override
    public boolean placeBid(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId, float bidAmount) {
        checkLogin();

        Ref<Item> item = lookupItem(tr, itemId);

        return doTransactionWithRetries(tr, ctx -> {
            var bid = new Bid(UUID.randomUUID(), bidAmount, user);
            boolean reserveMet = item.ref().placeBid(bid);
            user.ref().addWatchedAuction(item);
            return Option.apply(reserveMet);
        }).get();
    }

    @Override
    public void buyNow(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        checkLogin();

        Ref<Item> item = lookupItem(tr, itemId);

        doTransactionWithRetries(tr, ctx -> {
            item.ref().buyNow(user, item);
            return Option.apply(0);
        });
    }

    @Override
    public void endAuctionImmediately(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        Ref<Item> item = lookupItem(tr, itemId);

        doTransactionWithRetries(tr, ctx -> {
            item.ref().setEndDateToNow();
            item.ref().closeAuction(item);

            return Option.apply(0);
        });
    }

    @Override
    public String browseItemsByItemIds(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String[] itemIds) {
        checkLogin();

        // in MIXED and STRONG cases a deadlock can occur, since stringifying an item accesses strong state
        return doTransactionWithRetries(tr, ctx -> {
            List<Ref<Item>> items = new ArrayList<>(itemIds.length);
            for (String itemId : itemIds) {
                items.add(lookupItem(tr, itemId));
            }

            var sb = new StringBuilder("Items:\n");
            for (Ref<Item> item : items) {
                sb.append(item.ref().toString()).append("\n");
            }
            return Option.apply(sb.toString());
        }).get();
    }

    @Override
    public void rateUser(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String userId, int rating, String comment) {
        checkLogin();

        Ref<User> recipient = lookupUser(tr, userId);

        doTransaction(tr, ctx -> {
            user.ref().addRating(new Comment(rating, comment, user, recipient));
            return Option.apply(0);
        });
    }

    @Override
    public float getBidPrice(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        Ref<Item> item = lookupItem(tr, itemId);
        return doTransaction(tr, ctx -> Option.<Float>apply(item.ref().getTopBidPrice())).get();
    }

    @Override
    public ItemStatus getItemStatus(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        var item = lookupItem(tr, itemId);
        return doTransaction(tr, ctx -> Option.<ItemStatus>apply(item.ref().getStatus())).get();
    }

    @Override
    public String getItemSeller(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        var item = lookupItem(tr, itemId);
        return doTransaction(tr, ctx -> Option.apply(item.ref().getSeller().ref().getNickname())).get();
    }

    @Override
    public String getUser() {
        return userId;
    }

    public Ref<User> lookupUser(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String userId) {
        return doTransaction(tr, ctx ->
                Option.apply(ctx.lookup(makeUserAddress(userId), userConsistencyLevel, User.class))
        ).get();
    }

    public Ref<Item> lookupItem(TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr, String itemId) {
        return doTransaction(tr, ctx ->
                Option.apply(ctx.lookup(makeItemAddress(itemId), itemConsistencyLevel, Item.class))
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
