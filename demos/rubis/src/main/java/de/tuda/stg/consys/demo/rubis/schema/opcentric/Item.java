package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import scala.Option;

import java.io.Serializable;
import java.util.*;

public @Mixed class Item implements Serializable, IItem {
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
    private boolean soldViaBuyNow;
    private final Ref<@Mutable AuctionStore> auctionsStore;

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
        this.auctionsStore = null;
    }

    public Item(@Local UUID id, @Local @Mutable String name, @Mutable @Weak String description,
                @Local float reservePrice, @Local float initialPrice, @Local float buyNowPrice,
                @Local Date startDate, @Strong @Mutable Date endDate, @Local @Mutable Category category,
                Ref<@Mutable User> seller, Ref<@Mutable AuctionStore> auctionsStore) {
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
        this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.<Ref<@Mutable User>>empty(); // TODO
        this.auctionsStore = auctionsStore;
    }

    @Transactional
    @StrongOp
    public boolean placeBid(Bid bid) {
        if (seller.ref().refEquals(bid.getUser()))
            throw new AppException("You cannot bid on your own items.");

        if (new Date().after(endDate))
            throw new AppException.DateException("Auction has already ended.");

        if (!bid.getUser().ref().hasEnoughCredits(bid.getBid()))
            throw new AppException.NotEnoughCreditsException();

        if (bid.getBid() <= getTopBidPrice())
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");


        bids.add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice;
    }

    @Transactional
    @StrongOp
    public @Strong float buyNow(Ref<? extends @Mutable IUser> buyer, Ref<? extends @Mutable IItem> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item is different from this");

        if ((@Strong boolean)!bids.isEmpty() && getTopBidPrice() >= reservePrice)
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");

        if (seller.ref().refEquals(buyer))
            throw new AppException("You cannot buy your own items.");

        if (!buyer.ref().hasEnoughCredits(buyNowPrice))
            throw new AppException.NotEnoughCreditsException();


        endAuctionNow();
        this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.apply(toUserImpl(buyer));
        soldViaBuyNow = true;

        buyer.ref().removeBalance(buyNowPrice);
        seller.ref().addBalance(buyNowPrice);

        buyer.ref().addBoughtItem(item);
        seller.ref().closeOwnAuction(id, true);
        closeWatchedItemsForBidders();
        auctionsStore.ref().closeAuction(id, category);

        buyer.ref().notifyWinner(item, buyNowPrice);

        return buyNowPrice;
    }

    @StrongOp
    public void endAuctionNow() {
        endDate = new Date();
    }

    @Transactional
    @StrongOp
    public boolean closeAuction(Ref<? extends @Mutable IItem> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item different from this");

        if (new Date().before(endDate))
            throw new AppException.DateException("Auction has not yet ended.");


        @Strong boolean hasWinner = !(@Strong boolean)bids.isEmpty() && getTopBidPrice() >= reservePrice;
        if (hasWinner) {
            @Immutable @Strong Bid winningBid = bids.get(0);
            Ref<@Mutable User> buyer = toUserImpl(winningBid.getUser());
            this.buyer = (@Mutable @Weak Option<Ref<@Mutable User>>) Option.apply(buyer);
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            buyer.ref().notifyWinner(item, price);
        }

        seller.ref().closeOwnAuction(id, hasWinner);
        closeWatchedItemsForBidders();
        auctionsStore.ref().closeAuction(id, category);

        return hasWinner;
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
        return new ArrayList<>(bids);
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
        if (bids.isEmpty()) return Optional.empty();
        return Optional.of(bids.get(0));
    }

    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice;
    }

    @WeakOp @SideEffectFree
    public Ref<? extends IUser> getSeller() {
        return seller;
    }

    @WeakOp @SideEffectFree
    public @Local Optional<Ref<? extends @Mutable IUser>> getBuyer() {
        return Optional.ofNullable(buyer.getOrElse(null));
    }

    @WeakOp @SideEffectFree
    public boolean getSoldViaBuyNow() {
        return soldViaBuyNow;
    }

    @Transactional @SideEffectFree
    public boolean refEquals(Ref<? extends IItem> o) {
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

    @Transactional
    public void closeWatchedItemsForBidders() {
        for (Bid bid : bids) {
            Ref<? extends @Mutable IUser> bidder = bid.getUser();
            bidder.ref().closeWatchedAuction(id);
        }
    }

    private Ref<@Mutable User> toUserImpl(Ref<? extends @Mutable IUser> user) {
        return (Ref<@Mutable User>) user;  // TODO
    }
}
