package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import scala.Option;

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
    private Option<Ref<@Mutable User>> buyer; // cannot be null since we are serializing fields individually
    private final List<Bid> bids;
    private @Mutable @Weak ItemStatus status = ItemStatus.OPEN;

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
    }

    public Item(@Local UUID id,
                @Local @Mutable String name,
                @Mutable @Weak String description,
                @Local float reservePrice,
                @Local float initialPrice,
                @Local float buyNowPrice,
                @Local Date startDate,
                @Strong @Mutable Date endDate,
                @Local @Mutable Category category,
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
        this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.<Ref<@Mutable User>>empty(); // TODO
    }

    @StrongOp
    @Transactional
    public boolean placeBid(Bid bid) {
        if (seller.ref().refEquals(bid.getUser()))
            throw new AppException("You cannot bid on your own items.");

        if (endDate.before(new Date()))
            throw new AppException.DateException("Auction has already ended.");

        if (status != ItemStatus.OPEN)
            throw new AppException("Item is not available anymore.");

        if (!bid.getUser().ref().hasEnoughCredits(bid.getBid()))
            throw new AppException.NotEnoughCreditsException();

        if (bid.getBid() <= getTopBidPrice())
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");

        bids.add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice;
    }

    @StrongOp
    @Transactional
    public @Strong float buyNow(Ref<@Mutable User> buyer, Ref<@Mutable Item> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item is different from this");

        if (status != ItemStatus.OPEN)
            throw new AppException("Buy-Now is disabled, since item is not available anymore.");

        if (!bids.isEmpty() && getTopBidPrice() >= reservePrice)
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");

        if (seller.ref().refEquals(buyer))
            throw new AppException("You cannot buy your own items.");

        if (!buyer.ref().hasEnoughCredits(buyNowPrice))
            throw new AppException.NotEnoughCreditsException();

        setEndDateToNow();
        this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.apply(buyer);
        status = ItemStatus.SOLD_VIA_BUY_NOW;

        buyer.ref().removeBalance(buyNowPrice);
        seller.ref().addBalance(buyNowPrice);

        buyer.ref().addBoughtItem(item);
        seller.ref().closeOwnAuction(id, true);
        closeWatchedItemsForBidders();

        return buyNowPrice;
    }

    @StrongOp
    public void setEndDateToNow() {
        endDate = new Date();
    }

    @StrongOp
    @Transactional
    public boolean closeAuction(Ref<@Mutable Item> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item different from this");

        if (endDate.after(new Date()))
            throw new AppException.DateException("Auction has not yet ended.");

        if (status != ItemStatus.OPEN)
            throw new AppException("Auction is already closed.");

        @Strong boolean hasWinner = !(@Strong boolean)bids.isEmpty() && getTopBidPrice() >= reservePrice;
        if (hasWinner) {
            @Immutable @Strong Bid winningBid = bids.get(0);
            Ref<@Mutable User> buyer = winningBid.getUser();
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            status = ItemStatus.SOLD_VIA_AUCTION;
            this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.apply(buyer);
        } else {
            status = ItemStatus.NOT_SOLD;
        }

        seller.ref().closeOwnAuction(id, hasWinner);
        closeWatchedItemsForBidders();

        return hasWinner;
    }

    @StrongOp
    @Transactional
    public void closeWatchedItemsForBidders() {
        for (Bid bid : bids) {
            Ref<@Mutable User> bidder = bid.getUser();
            bidder.ref().closeWatchedAuction(id);
        }
    }

    @SideEffectFree
    public int getNumberOfBids() {
        return nBids;
    }

    @StrongOp
    @SideEffectFree
    public @Strong List<Bid> getAllBids() {
        return new ArrayList<>(bids);
    }

    @SideEffectFree
    public float getBuyNowPrice() {
        return buyNowPrice;
    }

    @StrongOp
    @SideEffectFree
    public @Strong float getTopBidPrice() {
        return bids.isEmpty() ? initialPrice : bids.get(0).getBid();
    }

    @StrongOp
    @SideEffectFree
    public @Local Optional<Bid> getTopBid() {
        if (bids.isEmpty()) return Optional.empty();
        return Optional.of(bids.get(0));
    }

    @SideEffectFree
    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice;
    }

    @SideEffectFree
    public boolean wasSoldViaBuyNow() {
        return status == ItemStatus.SOLD_VIA_BUY_NOW;
    }

    @SideEffectFree
    public @Weak UUID getId() { return id; }

    @SideEffectFree
    public String getName() {
        return name;
    }

    @SideEffectFree
    public Category getCategory() {
        return category;
    }

    @SideEffectFree
    public Date getEndDate() {
        return endDate;
    }

    @SideEffectFree
    public Ref<User> getSeller() {
        return seller;
    }

    @SideEffectFree
    public @Local Optional<Ref<@Mutable User>> getBuyer() {
        return Optional.ofNullable(buyer.getOrElse(null));
    }

    @SideEffectFree
    public ItemStatus getStatus() {
        return status;
    }

    public Date getStartDate() {
        return startDate;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(@Mutable @Weak String description) {
        this.description = description;
    }

    @Transactional
    @SideEffectFree
    public boolean refEquals(Ref<Item> o) {
        return o.ref().getId().equals(this.id);
    }

    @Override
    @SideEffectFree
    public String toString() {
        return "Item '" + name + "' (" + id + ")";
    }
}
