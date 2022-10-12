package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.*;

@SuppressWarnings({"consistency"})
public class RubisBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("rubis", RubisBenchmark.class, args);
    }

    private static final float maxPrice = 100;

    private final int numOfUsersPerReplica;
    private final List<Session> localSessions;
    private final List<Ref<? extends IUser>> users;
    private Ref<AuctionStore> auctionStore;


    public RubisBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.rubis.users");

        Session.userConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());
        Session.itemConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());
        Session.storeConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());

        localSessions = new ArrayList<>();
        users = new ArrayList<>();
    }

    private Category getRandomCategory() {
        return Category.values()[random.nextInt(Category.values().length)];
    }

    private float getRandomPrice() {
        return random.nextFloat() * maxPrice;
    }

    protected float getInitialBalance() {
        return numOfUsersPerReplica * nReplicas * maxPrice * 1.3f;
    }

    @Override
    public void setup() {
        Session.dataCentric = benchType == BenchmarkType.MIXED;
        if (benchType == BenchmarkType.MIXED) {
            Session.userImpl = de.tuda.stg.consys.demo.rubis.schema.datacentric.User.class;
            Session.itemImpl = de.tuda.stg.consys.demo.rubis.schema.datacentric.Item.class;
        } else {
            Session.userImpl = de.tuda.stg.consys.demo.rubis.schema.opcentric.User.class;
            Session.itemImpl = de.tuda.stg.consys.demo.rubis.schema.opcentric.Item.class;
        }

        // TODO: remove auction store
        if (processId() == 0) {
            store().transaction(ctx -> {
                auctionStore = ctx.replicate(Util.auctionStoreKey, Session.storeConsistencyLevel, AuctionStore.class);
                return Option.apply(0);
            });
        }
        barrier("auction_store_setup");
        if (processId() != 0) {
            store().transaction(ctx -> {
                auctionStore = ctx.lookup(Util.auctionStoreKey, Session.storeConsistencyLevel, AuctionStore.class);
                return Option.apply(0);
            });
        }

        System.out.println("Adding local users and items");
        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            var session = new Session(store());
            localSessions.add(session);

            session.registerUser(null, DemoUtils.addr("user", userIndex, processId()), DemoUtils.generateRandomName(),
                    DemoUtils.generateRandomPassword(), "mail@example.com");

            session.addBalance(null, getInitialBalance());

            session.registerItem(null, DemoUtils.generateRandomText(1), DemoUtils.generateRandomText(10),
                    getRandomCategory(), getRandomPrice(), 300);

            BenchmarkUtils.printProgress(userIndex);
        }

        barrier("users_added");

        System.out.println("Getting users and items from other replicas");
        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            for (int replicaIndex = 0; replicaIndex < nReplicas; replicaIndex++) {
                users.add(localSessions.get(0).findUser(null, DemoUtils.addr("user", userIndex, replicaIndex)));
            }
            BenchmarkUtils.printProgress(userIndex);
        }

        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        localSessions.clear();
        users.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                withExceptionHandling(this::browseCategory),
                withExceptionHandling(this::placeBid),
                withExceptionHandling(this::buyNow),
                withExceptionHandling(this::rateUser),
                withExceptionHandling(this::closeAuction)
        });
    }

    private Runnable withExceptionHandling(Runnable op) {
        return () -> {
            try {
                op.run();
            } catch (AppException e) {
                /* possible/acceptable errors:
                    - bidding on own item (rare)
                    - auction has already ended (common)
                */
                System.err.println(e.getMessage());
            }
        };
    }

    private void placeBid() {
        Session session = DemoUtils.getRandomElement(localSessions);

        store().transaction(ctx -> {
            List<Ref<? extends IItem>> openAuctions = auctionStore.ref().getOpenAuctions();
            if (openAuctions.isEmpty()) {
                System.err.println("no open auctions for placeBid operation");
                return Option.empty();
            }

            Ref<? extends IItem> item = DemoUtils.getRandomElement(openAuctions);
            float bid = session.getBidPrice(ctx, item);
            session.placeBid(ctx, item, bid * (1 + random.nextFloat()));
            return Option.apply(0);
        });
    }

    private void buyNow() {
        Session session = DemoUtils.getRandomElement(localSessions);

        Option<TransactionResult> result = store().transaction(ctx ->
        {
            List<Ref<? extends IItem>> openAuctions = auctionStore.ref().getOpenAuctions();
            if (openAuctions.isEmpty()) {
                System.err.println("no open auctions for buyNow operation");
                return Option.empty();
            }

            var item = DemoUtils.getRandomElement(openAuctions);

            var trxResult = !isTestMode ? new TransactionResult() : new TransactionResult(
                    new UserState[] {
                            new UserState(session.getLoggedInUser()),
                            new UserState(item.ref().getSeller()) },
                    new ItemState[] { new ItemState(item) });

            try {
                session.buyNow(ctx, item);
                return Option.apply(trxResult);
            } catch (IllegalArgumentException e) {
                trxResult.appExceptions = new Exception[] { e };
                System.err.println("Exception raised by app: " + e.getMessage());
                return Option.apply(trxResult);
            }
        });

        if (isTestMode && result.isDefined())
            buyNowTest(result.get());
    }

    private void buyNowTest(TransactionResult result) {
        if (result.appExceptions.length > 0) {
            check("no app exception occurred", false);
            return;
        } else {
            check("no app exception occurred", true);
        }

        store().transaction(ctx -> {
            UserState buyerPrev = result.users[0];
            Ref<? extends IUser> buyer = buyerPrev.ref;
            UserState sellerPrev = result.users[1];
            Ref<? extends IUser> seller = sellerPrev.ref;
            ItemState itemPrev = result.items[0];
            Ref<? extends IItem> item = itemPrev.ref;

            checkEquals("seller balance after buy-now",
                    sellerPrev.balance + item.ref().getBuyNowPrice(), seller.ref().getBalance());
            checkEquals("buyer balance after buy-now",
                    buyerPrev.balance - item.ref().getBuyNowPrice(), buyer.ref().getBalance());

            check("buy-now closed for seller",
                    seller.ref().getSellerHistory(true).stream().anyMatch(auction -> auction.ref().refEquals(item)));
            check("buy-now closed for seller (negated)",
                    seller.ref().getSellerHistory(false).stream().noneMatch(auction -> auction.ref().refEquals(item)));

            check("buyer gets item",
                    buyer.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(item)));

            var bids = item.ref().getAllBids();
            for (var bid : bids) {
                var bidder = bid.getUser();
                check("buy-now closed for bidder",
                        bidder.ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(item)));
            }
            return Option.apply(0);
        });
    }

    private void closeAuction() {
        Option<TransactionResult> result = store().transaction(ctx ->
        {
            List<Ref<? extends IItem>> openAuctions = auctionStore.ref().getOpenAuctions(); // TODO: is this ok? Overhead?
            if (openAuctions.isEmpty()) {
                System.out.println("no open auctions for closeAuction operation");
                return Option.empty();
            }

            Ref<? extends IItem> item = DemoUtils.getRandomElement(openAuctions);

            var trxResult = !isTestMode ? new TransactionResult() : new TransactionResult(
                    new UserState[] { new UserState(item.ref().getSeller()) },
                    new ItemState[] { new ItemState(item) });

            item.ref().endAuctionNow();
            try {
                item.ref().closeAuction(item);
            } catch (IllegalArgumentException e) {
                trxResult.appExceptions = new Exception[] { e };
                System.err.println("Exception raised by app: " + e.getMessage());
            }
            return Option.apply(trxResult);
        });

        if (isTestMode && result.isDefined())
            closeAuctionTest(result.get());
    }

    private void closeAuctionTest(TransactionResult result) {
        if (result.appExceptions.length > 0) {
            check("no app exception occurred", false);
            return;
        } else {
            check("no app exception occurred", true);
        }

        store().transaction(ctx -> {
            ItemState itemPrev = result.items[0];
            Ref<? extends IItem> item = itemPrev.ref;
            UserState sellerPrev = result.users[0];
            Ref<? extends IUser> seller = sellerPrev.ref;

            boolean wasSold = item.ref().getStatus() == IItem.Status.SOLD_VIA_AUCTION;
            float price = wasSold ? item.ref().getTopBidPrice() : 0;
            checkEquals("seller balance after closing auction", sellerPrev.balance + price, seller.ref().getBalance());

            check("auction closed for seller",
                    seller.ref().getSellerHistory(wasSold).stream().anyMatch(auction -> auction.ref().refEquals(item)));
            check("auction closed for seller (negated)",
                    seller.ref().getSellerHistory(!wasSold).stream().noneMatch(auction -> auction.ref().refEquals(item)));

            var bids = item.ref().getAllBids();
            for (var bid : bids) {
                var bidder = bid.getUser();
                check("auction closed for bidder",
                        bidder.ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(item)));
            }

            if (wasSold) {
                var topBid = item.ref().getTopBid();
                if (topBid.isEmpty()) {
                    check("winning bid not found", false);
                } else {
                    var winner = topBid.get().getUser();
                    check("winner gets item",
                            winner.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(item)));
                }
            }

            return Option.apply(0);
        });
    }

    private void browseCategory() {
        Category category = getRandomCategory();
        Session session = DemoUtils.getRandomElement(localSessions);
        session.browseCategory(null, category, 5);
    }

    private void rateUser() {
        int rating = 1 + random.nextInt(5);
        Ref<? extends IUser> user1 = DemoUtils.getRandomElement(users);
        Ref<? extends IUser> user2 = DemoUtils.getRandomElementExcept(users, user1);
        store().transaction(ctx -> {
            user1.ref().rate(new Comment(rating, DemoUtils.generateRandomText(10), user2, user1));
            return Option.apply(0);
        });
    }

    /**
     * Checked invariants:
     *  - ´user.balance´ is non-negative
     *  - ´user.balance´ corresponds to bought and sold items
     *  - auction winners corresponds to bought items
     *  - auction sellers correspond to sold items
     *  - winner is the highest bidder
     */
    @Override
    public void test() {
        if (processId() != 0) {
            printTestResult();
            return;
        }

        System.out.println("## TEST ##");

        check("users non empty", !users.isEmpty());

        store().transaction(ctx -> {
            for (var user : users) {

                float userBalance = user.ref().getBalance();
                check("balance >= 0", userBalance >= 0);

                float balance = getInitialBalance();
                for (var boughtItem : user.ref().getBuyerHistory()) {
                    if (boughtItem.ref().getSoldViaBuyNow()) {
                        balance -= boughtItem.ref().getBuyNowPrice();
                    } else {
                        var winningBidOption = boughtItem.ref().getTopBid();
                        check("buyer bid non null", winningBidOption.isPresent());
                        if (winningBidOption.isEmpty()) continue;

                        var winningBid = winningBidOption.get();
                        checkEquals("bid correct buyer", user.ref().getNickname(), winningBid.getUser().ref().getNickname());

                        var allBids = new ArrayList<>(boughtItem.ref().getAllBids());
                        allBids.remove(winningBid);
                        for (var bid : allBids) {
                            if (bid.getBid() >= winningBid.getBid())
                                check("winner bid is highest bid", false);
                        }

                        balance -= winningBid.getBid();
                    }
                }

                for (var soldItem : user.ref().getSellerHistory(true)) {
                    checkEquals("bid correct seller", user.ref().getNickname(), soldItem.ref().getSeller().ref().getNickname());

                    if (soldItem.ref().getSoldViaBuyNow()) {
                        balance += soldItem.ref().getBuyNowPrice();
                    } else {
                        var winningBidOption = soldItem.ref().getTopBid();
                        check("seller bid non null", winningBidOption.isPresent());
                        if (winningBidOption.isEmpty()) continue;

                        balance += winningBidOption.get().getBid();
                    }
                }

                checkFloatEquals("balance correct", balance, userBalance);
            }
            return Option.apply(0);
        });

        printTestResult();
    }

    private static class TransactionResult {
        Exception[] appExceptions = new Exception[] {};
        UserState[] users = new UserState[] {};
        ItemState[] items = new ItemState[] {};

        TransactionResult() {}

        TransactionResult(UserState[] users, ItemState[] items) {
            this.users = users;
            this.items = items;
        }
    }

    private static class UserState {
        final Ref<? extends IUser> ref;
        final float balance;

        UserState(Ref<? extends IUser> ref) {
            this.ref = ref;
            this.balance = ref.ref().getBalance();
        }
    }

    private static class ItemState {
        final Ref<? extends IItem> ref;

        ItemState(Ref<? extends IItem> ref) {
            this.ref = ref;
        }
    }
}
