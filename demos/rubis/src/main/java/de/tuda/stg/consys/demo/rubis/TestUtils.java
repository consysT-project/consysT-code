package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.demo.TestCollector;
import de.tuda.stg.consys.demo.rubis.schema.ISession;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import scala.Option;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

@SuppressWarnings({"consistency"})
public class TestUtils {
    public enum BenchType {
        DATA_CENTRIC,
        OP_CENTRIC
    }

    public static class TransactionResult {
        public Exception[] appExceptions = new Exception[] {};
        public UserTestInterface[] users = new TestUtils.UserTestInterface[] {};
        public ItemTestInterface[] items = new TestUtils.ItemTestInterface[] {};

        TransactionResult() {}

        TransactionResult(TestUtils.UserTestInterface[] users, TestUtils.ItemTestInterface[] items) {
            this.users = users;
            this.items = items;
        }

        public static TransactionResult empty() {
            return new TransactionResult();
        }

        public TransactionResult addUsers(ISession<?> session, String... userIds) {
            this.users = Arrays.stream(userIds).map(id -> new TestUtils.UserTestInterface(id, session)).toArray(UserTestInterface[]::new);
            return this;
        }

        public TransactionResult addItems(ISession<?> session, String... itemIds) {
            this.items = Arrays.stream(itemIds).map(id -> new TestUtils.ItemTestInterface(id, session)).toArray(ItemTestInterface[]::new);
            return this;
        }
    }

    public static class UserTestInterface {
        Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.User> refOpCentric;
        Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.User> refDataCentric;
        float prevBalance;

        public UserTestInterface(String userId, ISession<?> session) {
            if (benchType == BenchType.OP_CENTRIC) {
                this.refOpCentric = ((de.tuda.stg.consys.demo.rubis.schema.opcentric.Session) session).lookupUser(null, userId);
                this.prevBalance = refOpCentric.ref().getBalance();
            } else {
                this.refDataCentric = ((de.tuda.stg.consys.demo.rubis.schema.datacentric.Session) session).lookupUser(null, userId);
                this.prevBalance = refDataCentric.ref().getBalance();
            }
        }
    }

    public static class ItemTestInterface {
        Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.Item> refOpCentric;
        Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.Item> refDataCentric;

        public ItemTestInterface(String itemId, ISession<?> session) {
            if (benchType == BenchType.OP_CENTRIC) {
                this.refOpCentric = ((de.tuda.stg.consys.demo.rubis.schema.opcentric.Session) session).lookupItem(null, itemId);
            } else {
                this.refDataCentric = ((de.tuda.stg.consys.demo.rubis.schema.datacentric.Session) session).lookupItem(null, itemId);
            }
        }
    }

    public static Store store;
    public static BenchType benchType;

    static void closeAuctionTest(TransactionResult result) {
        if (result.appExceptions.length > 0) {
            TestCollector.check("no app exception occurred during close-auction", false);
            return;
        } else {
            TestCollector.check("no app exception occurred during close-auction", true);
        }

        store.transaction(ctx -> {
            Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.Item> itemOpCentric = result.items[0].refOpCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.User> sellerOpCentric = result.users[0].refOpCentric;

            Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.Item> itemDataCentric = result.items[0].refDataCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.User> sellerDataCentric = result.users[0].refDataCentric;

            boolean wasSold;

            if (benchType == BenchType.OP_CENTRIC) {
                wasSold = itemOpCentric.ref().getStatus() == ItemStatus.SOLD_VIA_AUCTION;
            } else {
                wasSold = itemDataCentric.ref().getStatus() == ItemStatus.SOLD_VIA_AUCTION;
            }

            if (benchType == BenchType.OP_CENTRIC) {
                TestCollector.check("auction closed for seller",
                        sellerOpCentric.ref().getSellerHistory(wasSold).stream().anyMatch(auction -> auction.ref().refEquals(itemOpCentric)));
            } else {
                TestCollector.check("auction closed for seller",
                        sellerDataCentric.ref().getSellerHistory(wasSold).stream().anyMatch(auction -> auction.ref().refEquals(itemDataCentric)));
            }

            if (benchType == BenchType.OP_CENTRIC) {
                TestCollector.check("auction closed for seller (negated)",
                        sellerOpCentric.ref().getSellerHistory(!wasSold).stream().noneMatch(auction -> auction.ref().refEquals(itemOpCentric)));
            } else {
                TestCollector.check("auction closed for seller (negated)",
                        sellerDataCentric.ref().getSellerHistory(!wasSold).stream().noneMatch(auction -> auction.ref().refEquals(itemDataCentric)));
            }

            if (benchType == BenchType.OP_CENTRIC) {
                for (var bid : itemOpCentric.ref().getAllBids()) {
                    TestCollector.check("auction closed for bidder",
                            bid.getUser().ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(itemOpCentric)));
                }
            } else {
                for (var bid : itemDataCentric.ref().getAllBids()) {
                    TestCollector.check("auction closed for bidder",
                            bid.getUser().ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(itemDataCentric)));
                }
            }

            if (wasSold) {
                if (benchType == BenchType.OP_CENTRIC) {
                    var topBid = itemOpCentric.ref().getTopBid();
                    if (topBid.isEmpty()) {
                        TestCollector.check("winning bid not found", false);
                    } else {
                        var winner = topBid.get().getUser();
                        TestCollector.check("winner gets item",
                                winner.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(itemOpCentric)));
                    }
                } else {
                    var topBid = itemDataCentric.ref().getTopBid();
                    if (topBid.isEmpty()) {
                        TestCollector.check("winning bid not found", false);
                    } else {
                        var winner = topBid.get().getUser();
                        TestCollector.check("winner gets item",
                                winner.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(itemDataCentric)));
                    }
                }
            }

            return Option.apply(0);
        });
    }

    static void buyNowTest(TransactionResult result) {
        if (result.appExceptions.length > 0) {
            TestCollector.check("no app exception occurred during buy-now", false);
            return;
        } else {
            TestCollector.check("no app exception occurred during buy-now", true);
        }

        store.transaction(ctx -> {
            Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.Item> itemOpCentric = result.items[0].refOpCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.User> buyerOpCentric = result.users[0].refOpCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.User> sellerOpCentric = result.users[1].refOpCentric;

            Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.Item> itemDataCentric = result.items[0].refDataCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.User> buyerDataCentric = result.users[0].refDataCentric;
            Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.User> sellerDataCentric = result.users[1].refDataCentric;

            /* TODO: not testable due to possible parallel operations
            float prevBalance = result.users[0].prevBalance;
            checkFloatEquals("seller balance after buy-now",
                    sellerPrev.balance + item.ref().getBuyNowPrice(), seller.ref().getBalance(), 0.01f);
            checkFloatEquals("buyer balance after buy-now",
                    buyerPrev.balance - item.ref().getBuyNowPrice(), buyer.ref().getBalance(), 0.01f);
             */

            if (benchType == BenchType.OP_CENTRIC) {
                TestCollector.check("buy-now closed for seller",
                        sellerOpCentric.ref().getSellerHistory(true).stream().anyMatch(auction -> auction.ref().refEquals(itemOpCentric)));
            } else {
                TestCollector.check("buy-now closed for seller",
                        sellerDataCentric.ref().getSellerHistory(true).stream().anyMatch(auction -> auction.ref().refEquals(itemDataCentric)));
            }

            if (benchType == BenchType.OP_CENTRIC) {
                TestCollector.check("buy-now closed for seller (negated)",
                        sellerOpCentric.ref().getSellerHistory(false).stream().noneMatch(auction -> auction.ref().refEquals(itemOpCentric)));
            } else {
                TestCollector.check("buy-now closed for seller (negated)",
                        sellerDataCentric.ref().getSellerHistory(false).stream().noneMatch(auction -> auction.ref().refEquals(itemDataCentric)));
            }

            if (benchType == BenchType.OP_CENTRIC) {
                TestCollector.check("buyer gets item",
                        buyerOpCentric.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(itemOpCentric)));
            } else {
                TestCollector.check("buyer gets item",
                        buyerDataCentric.ref().getBuyerHistory().stream().anyMatch(auction -> auction.ref().refEquals(itemDataCentric)));
            }


            if (benchType == BenchType.OP_CENTRIC) {
                for (var bid : itemOpCentric.ref().getAllBids()) {
                    TestCollector.check("buy-now closed for bidder",
                            bid.getUser().ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(itemOpCentric)));
                }
            } else {
                for (var bid : itemDataCentric.ref().getAllBids()) {
                    TestCollector.check("buy-now closed for bidder",
                            bid.getUser().ref().getOpenBuyerAuctions().stream().noneMatch(auction -> auction.ref().refEquals(itemDataCentric)));
                }
            }

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
    static void finalTest(List<String> users, float initialBalance, ISession session) {
        store.transaction(ctx -> {
            for (var userId : users) {
                Ref<de.tuda.stg.consys.demo.rubis.schema.opcentric.User> userOpCentric;
                Ref<de.tuda.stg.consys.demo.rubis.schema.datacentric.User> userDataCentric;

                if (benchType == BenchType.OP_CENTRIC) {
                    userOpCentric = ((de.tuda.stg.consys.demo.rubis.schema.opcentric.Session) session).lookupUser(ctx, userId);
                    userDataCentric = null;
                } else {
                    userDataCentric = ((de.tuda.stg.consys.demo.rubis.schema.datacentric.Session) session).lookupUser(ctx, userId);
                    userOpCentric = null;
                }

                float userBalance;
                if (isOpCentric()) {
                    userBalance = userOpCentric.ref().getBalance();
                } else {
                    userBalance = userDataCentric.ref().getBalance();
                }

                TestCollector.check("balance >= 0", userBalance >= 0);

                float balance = initialBalance;

                if (benchType == BenchType.OP_CENTRIC) {
                    for (var boughtItem : userOpCentric.ref().getBuyerHistory()) {
                        if (boughtItem.ref().wasSoldViaBuyNow()) {
                            balance -= boughtItem.ref().getBuyNowPrice();
                        } else {
                            var winningBidOption = boughtItem.ref().getTopBid();
                            TestCollector.check("buyer bid non null", winningBidOption.isPresent());
                            if (winningBidOption.isEmpty()) continue;

                            var winningBid = winningBidOption.get();
                            TestCollector.checkEquals("bid correct buyer", userOpCentric.ref().getNickname(), winningBid.getUser().ref().getNickname());

                            var allBids = new ArrayList<>(boughtItem.ref().getAllBids());
                            allBids.remove(winningBid);
                            for (var bid : allBids) {
                                if (bid.getBid() >= winningBid.getBid())
                                    TestCollector.check("winner bid is highest bid", false);
                            }

                            balance -= winningBid.getBid();
                        }
                    }
                } else {
                    for (var boughtItem : userDataCentric.ref().getBuyerHistory()) {
                        if (boughtItem.ref().wasSoldViaBuyNow()) {
                            balance -= boughtItem.ref().getBuyNowPrice();
                        } else {
                            var winningBidOption = boughtItem.ref().getTopBid();
                            TestCollector.check("buyer bid non null", winningBidOption.isPresent());
                            if (winningBidOption.isEmpty()) continue;

                            var winningBid = winningBidOption.get();
                            TestCollector.checkEquals("bid correct buyer", userDataCentric.ref().getNickname(), winningBid.getUser().ref().getNickname());

                            var allBids = new ArrayList<>(boughtItem.ref().getAllBids());
                            allBids.remove(winningBid);
                            for (var bid : allBids) {
                                if (bid.getBid() >= winningBid.getBid())
                                    TestCollector.check("winner bid is highest bid", false);
                            }

                            balance -= winningBid.getBid();
                        }
                    }
                }

                if (benchType == BenchType.OP_CENTRIC) {
                    for (var soldItem : userOpCentric.ref().getSellerHistory(true)) {
                        TestCollector.checkEquals("bid correct seller", userOpCentric.ref().getNickname(), soldItem.ref().getSeller().ref().getNickname());

                        if (soldItem.ref().wasSoldViaBuyNow()) {
                            balance += soldItem.ref().getBuyNowPrice();
                        } else {
                            var winningBidOption = soldItem.ref().getTopBid();
                            TestCollector.check("seller bid non null", winningBidOption.isPresent());
                            if (winningBidOption.isEmpty()) continue;

                            balance += winningBidOption.get().getBid();
                        }
                    }
                } else {
                    for (var soldItem : userDataCentric.ref().getSellerHistory(true)) {
                        TestCollector.checkEquals("bid correct seller", userDataCentric.ref().getNickname(), soldItem.ref().getSeller().ref().getNickname());

                        if (soldItem.ref().wasSoldViaBuyNow()) {
                            balance += soldItem.ref().getBuyNowPrice();
                        } else {
                            var winningBidOption = soldItem.ref().getTopBid();
                            TestCollector.check("seller bid non null", winningBidOption.isPresent());
                            if (winningBidOption.isEmpty()) continue;

                            balance += winningBidOption.get().getBid();
                        }
                    }
                }


                TestCollector.checkFloatEquals("balance correct", balance, userBalance, 0.01f);
            }
            return Option.apply(0);
        });
    }

    private static boolean isOpCentric() {
        return benchType == BenchType.OP_CENTRIC;
    }
}
