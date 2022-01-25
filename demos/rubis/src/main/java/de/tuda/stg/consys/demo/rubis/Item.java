package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.*;

public class Item implements Serializable {
    private final UUID id;
    private final String name;
    private String description;
    private int quantity;
    private final float reservePrice;
    private float initialPrice;
    private float buyNowPrice;
    private int nBids;
    private Date startDate;
    private Date endDate;
    private Category category;
    private final Ref<User> seller;
    private final List<Ref<Bid>> bids; // TODO could also only store best bid
    private final List<Ref<Bid>> autoBids;

    public Item(UUID id, String name, String description, int quantity, float reservePrice, float initialPrice,
                float buyNowPrice, Date startDate, Date endDate, Category category, Ref<User> seller) {
        this.id = id;
        this.name = name;
        this.description = description;
        //this.quantity = quantity;
        this.reservePrice = reservePrice;
        this.initialPrice = initialPrice;
        this.buyNowPrice = buyNowPrice;
        this.startDate = startDate;
        this.endDate = endDate;
        this.category = category;
        this.seller = seller;
        this.bids = new Stack<>();
        this.autoBids = new LinkedList<>(); // TODO: how/where to make new bid items?
    }

    @Transactional
    @StrongOp
    public void placeBid(Ref<Bid> bid) {
        if (new Date().after(endDate)) {
            System.out.println("Auction has already ended.");
            return;
        }

        float maxBid = bids.isEmpty() ? initialPrice : bids.get(0).ref().getBid();
        if ((float)bid.ref().getBid() <= maxBid) {
            System.out.println("Minimum necessary bid amount not met.");
            return;
        }

        bids.add(0, bid);
        nBids++;

        //if ((int)bid.ref().maxBid > 0) {
        //    autoBids.add(bid);
        //}
        // autoBids.notify(newMaxBid)
    }

    @Transactional
    public void buyNow(Ref<User> buyer) {
        if (!bids.isEmpty() && (int)bids.get(0).ref().getBid() >= reservePrice) {
            System.out.println("Buy now disabled, since reserve price is already met.");
        } else {
            buyer.ref().removeBalance(buyNowPrice);
        }
    }

    @Transactional
    @StrongOp
    public void closeAuction() {
        if (new Date().before(endDate)) {
            System.out.println("Auction has not yet ended.");
            return;
        }

        var winningBid = bids.get(0);
        ((Ref<User>)winningBid.ref().getUser()).ref().removeBalance(winningBid.ref().getBid());
        // TODO: winningBid.ref().user.ref().notifyWinner();
    }

    @WeakOp
    public int getNumberOfBids() {
        return nBids;
    }

    @WeakOp
    public Category getCategory() {
        return category;
    }

    @WeakOp
    public String getName() {
        return name;
    }

    @WeakOp
    public Date getEndDate() {
        return endDate;
    }

    @WeakOp
    public float getBuyNowPrice() {
        return buyNowPrice;
    }

    @WeakOp
    public float getBiddingPrice() {
        return bids.get(0).ref().getBid();
    }

    @WeakOp
    public Ref<User> getSeller() {
        return seller;
    }
}
