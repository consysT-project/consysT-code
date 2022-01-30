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
    private final float reservePrice;
    private final float initialPrice;
    private final float buyNowPrice;
    private int nBids;
    private final Date startDate;
    private Date endDate;
    private final Category category;
    private final Ref<User> seller;
    private final List<Ref<Bid>> bids;

    public Item(UUID id, String name, String description, float reservePrice, float initialPrice,
                float buyNowPrice, Date startDate, Date endDate, Category category, Ref<User> seller) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.reservePrice = reservePrice;
        this.initialPrice = initialPrice;
        this.buyNowPrice = buyNowPrice;
        this.startDate = startDate;
        this.endDate = endDate;
        this.category = category;
        this.seller = seller;
        this.bids = new LinkedList<>();
    }

    @Transactional
    @StrongOp
    public boolean placeBid(Ref<Bid> bid) {
        if (new Date().after(endDate)) {
            throw new DateException("Auction has already ended.");
        }

        if ((float)bid.ref().getBid() <= getTopBidPrice()) {
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.ref().getBid() + ")");
        }

        bids.add(0, bid);
        nBids++;

        return (float)bid.ref().getBid() >= reservePrice;
    }

    @Transactional
    @StrongOp
    public float buyNow() {
        if (!bids.isEmpty() && getTopBidPrice() >= reservePrice) {
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");
        } else {
            endAuctionNow();
            return buyNowPrice;
        }
    }

    @StrongOp
    public void endAuctionNow() {
        endDate = new Date();
    }

    @Transactional
    @StrongOp
    public Optional<Ref<Bid>> closeAuction() {
        if (new Date().before(endDate)) {
            throw new DateException("Auction has not yet ended.");
        }

        if (bids.isEmpty() || getTopBidPrice() < reservePrice) {
            return Optional.empty();
        } else {
            return Optional.of(bids.get(0));
        }
    }

    @WeakOp
    public void setDescription(String description) {
        this.description = description;
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
    public UUID getId() { return id; }

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
    public float getTopBidPrice() {
        return bids.isEmpty() ? initialPrice : bids.get(0).ref().getBid();
    }

    @WeakOp
    public Optional<Ref<Bid>> getTopBid() {
        return bids.isEmpty() ? Optional.empty() : Optional.of(bids.get(0));
    }

    @WeakOp
    public Ref<User> getSeller() {
        return seller;
    }

    @WeakOp
    public String toString() {
        return "Item '" + name + "' (" + id + ")\n" +
                "  - price (bid | Buy-Now): " + getTopBidPrice() + " | " + getBuyNowPrice() + "\n" +
                "  - auction duration: " + startDate + " - " + endDate + "\n" +
                "  - number of bids: " + getNumberOfBids() + "\n" +
                description;
    }
}
