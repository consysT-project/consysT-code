package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

public class Util {
    public static final String auctionStoreKey = "root";

    @Transactional
    public static void closeAuction(Ref<@Mutable Item> item, Ref<@Mutable AuctionStore> rubis) {
        Ref<@Mutable User> seller = item.ref().getSeller();
        @Immutable @Strong Optional<Bid> winningBid = item.ref().closeAuction();
        @Strong boolean hasWinner = (@Strong boolean)winningBid.isPresent(); // no good way to model return type of Optional

        if (hasWinner) {
            Ref<@Mutable User> winner = winningBid.get().getUser();
            @Strong float price = winningBid.get().getBid();

            winner.ref().removeBalance(price);
            seller.ref().addBalance(price);

            winner.ref().closeWatchedAuction(item, true);

            winner.ref().notifyWinner(item, price);
        }

        seller.ref().closeOwnAuction(item, hasWinner);
        closeWatchedItemsForBidders(item);
        rubis.ref().closeAuction(item.ref().getId(), item.ref().getCategory());
    }

    @Transactional
    public static void buyItemNow(Ref<@Mutable Item> item, Ref<@Mutable User> buyer, Ref<@Mutable AuctionStore> rubis) {
        @Strong float price = item.ref().buyNow();

        if (!hasEnoughCredits(buyer, price)) {
            throw new AppException.NotEnoughCreditsException();
        }

        Ref<@Mutable User> seller = item.ref().getSeller();
        buyer.ref().removeBalance(price);
        seller.ref().addBalance(price);

        buyer.ref().closeWatchedAuction(item, true);
        seller.ref().closeOwnAuction(item, true);
        closeWatchedItemsForBidders(item);

        buyer.ref().notifyWinner(item, price);

        rubis.ref().closeAuction(item.ref().getId(), item.ref().getCategory());
    }

    @Transactional
    public static boolean hasEnoughCredits(Ref<User> buyer, float price) {
        @Immutable @Strong List<Ref<Item>> watched = buyer.ref().getOpenBuyerAuctions();
        float potentialBalance = buyer.ref().getBalance();

        for (var item : watched) {
            @Immutable @Strong Optional<Bid> bid = item.ref().getTopBid();
            if ((@Strong boolean)bid.isPresent() && (@Strong boolean)(bid.get().getUser()).ref().refEquals(buyer)) {
                potentialBalance -= bid.get().getBid();
            }
        }

        return potentialBalance >= price;
    }

    @Transactional
    private static void closeWatchedItemsForBidders(Ref<@Mutable Item> item) {
        @Immutable @Strong List<Bid> bids = item.ref().getAllBids();
        for (Bid bid : bids) {
            Ref<@Mutable User> bidder = bid.getUser();
            bidder.ref().closeWatchedAuction(item, false);
        }
    }
}
