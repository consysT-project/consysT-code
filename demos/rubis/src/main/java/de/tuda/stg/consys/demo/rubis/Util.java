package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

public class Util {
    @Transactional
    public static void closeAuction(Ref<Item> item, Ref<Rubis> rubis) {
        Ref<User> seller = item.ref().getSeller();
        Ref<Bid> winningBid = item.ref().closeAuction();

        if (winningBid != null) {
            Ref<User> winner = winningBid.ref().getUser();
            float price = winningBid.ref().getBid();

            winner.ref().removeBalance(price); // TODO: negative balance handling
            seller.ref().addBalance(price);

            winner.ref().closeBuyerAuction(item);
        }

        seller.ref().closeSellerAuction(item);
        rubis.ref().closeAuction(item.ref().getId(), item.ref().getCategory());
    }

    @Transactional
    public static void buyItemNow(Ref<Item> item, Ref<User> buyer, Ref<Rubis> rubis) {
        float price;
        try {
            price = item.ref().buyNow();
        } catch (IllegalArgumentException e) {
            System.out.println(e.getMessage());
            return;
        }

        Ref<User> seller = item.ref().getSeller();
        buyer.ref().removeBalance(price);
        seller.ref().addBalance(price);

        rubis.ref().closeAuction(item.ref().getId(), item.ref().getCategory());
    }
}
