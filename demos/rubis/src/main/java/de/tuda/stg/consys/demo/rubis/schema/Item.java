package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Mixed class Item implements Serializable {
    private final @Immutable UUID id;
    private final String name;
    private String description;
    private final float reservePrice;
    private final float initialPrice;
    private final float buyNowPrice;
    private int nBids;
    private final @Immutable Date startDate;
    private Date endDate;
    private final @Immutable Category category;
    private final Ref<@Mutable User> seller;
    private final List<Bid> bids;
    private boolean soldViaBuyNow;

    public Item() {
        this.id = null;
        this.name = "";
        this.reservePrice = 0;
        this.initialPrice = 0;
        this.buyNowPrice = 0;
        this.startDate = null;
        this.category = null;
        this.seller = null;
        this.bids = null;
        this.soldViaBuyNow = false;
    }

    public Item(@Local UUID id, @Local @Mutable String name, @Mutable @Weak String description,
                @Local float reservePrice, @Local float initialPrice, @Local float buyNowPrice,
                @Local Date startDate, @Strong @Mutable Date endDate, @Local @Mutable Category category,
                Ref<@Mutable User> seller) {
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
        this.soldViaBuyNow = false;
    }

    @Transactional
    @StrongOp
    public boolean placeBid(Bid bid) {
        if (new Date().after(endDate)) {
            throw new AppException.DateException("Auction has already ended.");
        }

        if (bid.getBid() <= getTopBidPrice()) {
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");
        }

        bids.add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice;
    }

    @Transactional
    @StrongOp
    public @Strong float buyNow() {
        if ((@Strong boolean)!bids.isEmpty() && getTopBidPrice() >= reservePrice) {
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");
        } else {
            endAuctionNow();
            soldViaBuyNow = true;
            return buyNowPrice;
        }
    }

    @StrongOp
    public void endAuctionNow() {
        endDate = new Date();
    }

    @Transactional
    @StrongOp
    public @Strong Optional<Bid> closeAuction() {
        if (new Date().before(endDate)) {
            throw new AppException.DateException("Auction has not yet ended.");
        }

        if ((@Strong boolean)bids.isEmpty() || getTopBidPrice() < reservePrice) {
            return Optional.empty();
        } else {
            return Optional.of(bids.get(0));
        }
    }

    @WeakOp
    public void setDescription(@Mutable @Weak String description) {
        this.description = description;
    }

    @WeakOp @SideEffectFree
    public int getNumberOfBids() {
        return nBids;
    }

    @StrongOp @SideEffectFree
    public List<Bid> getAllBids() {
        return bids;
    }

    @WeakOp @SideEffectFree
    public Category getCategory() {
        return category;
    }

    @WeakOp @SideEffectFree
    public UUID getId() { return id; }

    @WeakOp @SideEffectFree
    public String getName() {
        return name;
    }

    @WeakOp @SideEffectFree
    public Date getEndDate() {
        return endDate;
    }

    @WeakOp @SideEffectFree
    public float getBuyNowPrice() {
        return buyNowPrice;
    }

    @StrongOp @SideEffectFree
    public @Strong float getTopBidPrice() {
        return bids.isEmpty() ? initialPrice : bids.get(0).getBid();
    }

    @StrongOp @SideEffectFree
    public @Local Optional<Bid> getTopBid() {
        if (bids.isEmpty()) return Optional.<Bid>empty();
        return Optional.<Bid>of(bids.get(0));
    }

    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice;
    }

    @WeakOp @SideEffectFree
    public Ref<@Mutable User> getSeller() {
        return seller;
    }

    @WeakOp @SideEffectFree
    public boolean getSoldViaBuyNow() {
        return soldViaBuyNow;
    }

    @Transactional @SideEffectFree
    public @Local boolean refEquals(Ref<Item> o) {
        return o.ref().getId().equals(this.id);
    }

    @WeakOp @SideEffectFree @Transactional
    public String toString() {
        return "Item '" + name + "' (" + id + ")\n" +
                "  - price (bid | Buy-Now): " + getTopBidPrice() + " | " + getBuyNowPrice() + "\n" +
                "  - auction duration: " + startDate + " - " + endDate + "\n" +
                "  - number of bids: " + getNumberOfBids() + "\n" +
                description;
    }
}
