package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Weak class Item implements Serializable {
    private final @Immutable UUID id;
    private final String name;
    private String description;
    private final Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> reservePrice;
    private final Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> initialPrice;
    private final Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> buyNowPrice;
    private int nBids;
    private final @Immutable Date startDate;
    private final Ref<@Strong @Mutable Date> endDate;
    private final @Immutable Category category;
    private final Ref<@Mutable User> seller;
    private Ref<@Mutable User> buyer;
    private final Ref<@Strong @Mutable List<Bid>> bids;
    private final Ref<@Strong @Mutable StatusBox> status;

    public Item(@Local UUID id,
                @Weak @Mutable String name,
                @Mutable @Weak String description,
                Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> reservePrice,
                Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> initialPrice,
                Ref<@Immutable @Strong NumberBox<@Mutable @Strong Float>> buyNowPrice,
                @Local Date startDate,
                Ref<@Strong @Mutable Date> endDate,
                @Local @Mutable Category category,
                Ref<@Mutable User> seller,
                Ref<@Strong @Mutable List<Bid>> bids,
                Ref<@Strong @Mutable StatusBox> status) {
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
        this.bids = bids;
        this.status = status;
        this.buyer = null;
    }

    @Transactional
    public boolean placeBid(Bid bid) {
        if (seller.ref().refEquals(((@Weak Bid) bid).getUser()))
            throw new AppException("You cannot bid on your own items.");

        if (endDate.ref().before(new Date()))
            throw new AppException.DateException("Auction has already ended.");

        if (status.ref().value != ItemStatus.OPEN)
            throw new AppException("Item is not available anymore.");

        if (!bid.getUser().ref().hasEnoughCredits(bid.getBid()))
            throw new AppException.NotEnoughCreditsException();

        if (bid.getBid() <= getTopBidPrice())
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");

        bids.ref().add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice.ref().floatValue();
    }

    @Transactional
    public @Strong float buyNow(Ref<@Mutable User> buyer, Ref<@Mutable Item> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item is different from this");

        if (status.ref().value != ItemStatus.OPEN)
            throw new AppException("Buy-Now is disabled, since item is not available anymore.");

        if (!bids.ref().isEmpty() && getTopBidPrice() >= reservePrice.ref().floatValue())
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");

        if (seller.ref().refEquals(buyer))
            throw new AppException("You cannot buy your own items.");

        if (!buyer.ref().hasEnoughCredits(buyNowPrice.ref().floatValue()))
            throw new AppException.NotEnoughCreditsException();

        setEndDateToNow();
        this.buyer = (Ref<@Mutable User>) buyer; // TODO: might be problematic since the reference is weak?
        status.ref().value = ItemStatus.SOLD_VIA_BUY_NOW;

        buyer.ref().removeBalance(buyNowPrice.ref().floatValue());
        seller.ref().addBalance(buyNowPrice.ref().floatValue());

        buyer.ref().addBoughtItem(item);
        seller.ref().closeOwnAuction(id, true);
        closeWatchedItemsForBidders();

        return buyNowPrice.ref().floatValue();
    }

    @Transactional
    public void setEndDateToNow() {
        endDate.ref().setTime(new Date().getTime());
    }

    @Transactional
    public boolean closeAuction(Ref<@Mutable Item> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item different from this");

        if (endDate.ref().after(new Date()))
            throw new AppException.DateException("Auction has not yet ended.");

        if (status.ref().value != ItemStatus.OPEN)
            throw new AppException("Auction is already closed.");

        @Strong boolean hasWinner = !(@Strong boolean)bids.ref().isEmpty() && getTopBidPrice() >= reservePrice.ref().floatValue();
        if (hasWinner) {
            @Immutable @Strong Bid winningBid = bids.ref().get(0);
            Ref<@Mutable User> buyer = winningBid.getUser();
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            status.ref().value = ItemStatus.SOLD_VIA_AUCTION;
            this.buyer = (Ref<@Mutable User>) winningBid.getUser();
        } else {
            status.ref().value = ItemStatus.NOT_SOLD;
        }

        seller.ref().closeOwnAuction(id, hasWinner);
        closeWatchedItemsForBidders();

        return hasWinner;
    }

    @Transactional
    public void closeWatchedItemsForBidders() {
        for (Bid bid : getAllBids()) {
            Ref<@Mutable User> bidder = bid.getUser();
            bidder.ref().closeWatchedAuction(id);
        }
    }

    @SideEffectFree
    public int getNumberOfBids() {
        return nBids;
    }

    @Transactional
    @SideEffectFree
    public @Strong List<Bid> getAllBids() {
        if (bids.ref().isEmpty())
            return new LinkedList<>();
        return bids.ref().subList(0, bids.ref().size() - 1); // TODO
    }

    @Transactional
    @SideEffectFree
    public float getBuyNowPrice() {
        return buyNowPrice.ref().floatValue();
    }

    @Transactional
    @SideEffectFree
    public @Strong float getTopBidPrice() {
        return bids.ref().isEmpty() ? initialPrice.ref().floatValue() : bids.ref().get(0).getBid();
    }

    @Transactional
    @SideEffectFree
    public @Local Optional<Bid> getTopBid() {
        if (bids.ref().isEmpty()) return Optional.empty();
        return Optional.of(bids.ref().get(0));
    }

    @Transactional
    @SideEffectFree
    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice.ref().floatValue();
    }

    @Transactional
    @SideEffectFree
    public boolean wasSoldViaBuyNow() {
        return status.ref().value == ItemStatus.SOLD_VIA_BUY_NOW;
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

    @Transactional
    @SideEffectFree
    public Date getEndDate() {
        return new Date(endDate.ref().getTime());
    }

    @SideEffectFree
    public Ref<User> getSeller() {
        return seller;
    }

    @SideEffectFree
    public @Local Optional<Ref<@Mutable User>> getBuyer() {
        return Optional.ofNullable(buyer);
    }

    @Transactional
    @SideEffectFree
    public ItemStatus getStatus() {
        return status.ref().value;
    }

    @SideEffectFree
    public Date getStartDate() {
        return startDate;
    }

    @SideEffectFree
    public String getDescription() {
        return description;
    }

    @SideEffectFree
    public void setDescription(@Mutable @Weak String description) {
        this.description = description;
    }

    @Transactional
    @SideEffectFree
    public @Weak boolean refEquals(Ref<Item> o) {
        return o.ref().getId().equals(this.id);
    }

    @Override
    @Transactional
    @SideEffectFree
    public String toString() {
        return "Item '" + name + "' (" + id + ")\n" +
                "  - price (bid | Buy-Now): " + getTopBidPrice() + " | " + getBuyNowPrice() + "\n" +
                "  - auction duration: " + startDate + " - " + endDate + "\n" +
                "  - number of bids: " + getNumberOfBids() + "\n" +
                description;
    }
}
