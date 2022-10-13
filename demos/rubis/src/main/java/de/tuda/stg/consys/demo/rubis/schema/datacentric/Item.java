package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Weak class Item implements Serializable, IItem {
    private final @Immutable UUID id;
    private final String name;
    private String description;
    private final float reservePrice; // TODO can't model as strong/local in weak class
    private final float initialPrice; // TODO
    private final float buyNowPrice; // TODO
    private int nBids;
    private final @Immutable Date startDate;
    private Ref<@Strong @Mutable Date> endDate;
    private final @Immutable Category category;
    private final Ref<@Mutable User> seller;
    private Ref<@Mutable User> buyer;
    private final Ref<@Strong @Mutable RefList<Bid>> bids;
    // we have to cast here because of a checker-framework bug where enum constants cannot be annotated
    private Status status = (@MutableBottom @Local Status) Status.OPEN;

    public Item(@Local UUID id, @Weak @Mutable String name, @Mutable @Weak String description,
                @Local float reservePrice, @Local float initialPrice, @Local float buyNowPrice,
                @Local Date startDate, Ref<@Strong @Mutable Date> endDate, @Local @Mutable Category category,
                Ref<@Mutable User> seller,
                Ref<@Strong @Mutable RefList<Bid>> bids) {
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
        this.buyer = null;
    }

    @Transactional
    @StrongOp
    public boolean placeBid(Bid bid) {
        if (seller.ref().refEquals(bid.getUser()))
            throw new AppException("You cannot bid on your own items.");

        if ((@Strong boolean) endDate.ref().before(new Date()))
            throw new AppException.DateException("Auction has already ended.");

        if (status != Status.OPEN)
            throw new AppException("Item is not available anymore.");

        if (!bid.getUser().ref().hasEnoughCredits(bid.getBid()))
            throw new AppException.NotEnoughCreditsException();

        if (bid.getBid() <= getTopBidPrice())
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");


        bids.ref().add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice;
    }

    @Transactional
    @StrongOp
    public @Strong float buyNow(Ref<? extends @Mutable IUser> buyer, Ref<? extends @Mutable IItem> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item is different from this");

        if (status != Status.OPEN)
            throw new AppException("Buy-Now is disabled, since item is not available anymore.");

        if ((@Strong boolean)!bids.ref().isEmpty() && getTopBidPrice() >= (@Strong float) reservePrice)
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");

        if (seller.ref().refEquals(buyer))
            throw new AppException("You cannot buy your own items.");

        if (!buyer.ref().hasEnoughCredits((@Strong float) buyNowPrice))
            throw new AppException.NotEnoughCreditsException();


        endAuctionNow();
        this.buyer = (Ref<@Mutable User>) buyer;
        status = (@MutableBottom @Local Status) Status.SOLD_VIA_BUY_NOW;

        buyer.ref().removeBalance((@Strong float) buyNowPrice);
        seller.ref().addBalance((@Strong float) buyNowPrice);

        buyer.ref().addBoughtItem(item);
        seller.ref().closeOwnAuction(id, true);
        closeWatchedItemsForBidders();

        buyer.ref().notifyWinner(item, buyNowPrice);

        return (@Strong float) buyNowPrice;
    }

    @StrongOp @Transactional
    public void endAuctionNow() {
        endDate.ref().setTime(new Date().getTime());
    }

    @Transactional
    @StrongOp
    public boolean closeAuction(Ref<? extends @Mutable IItem> item) {
        if (!this.refEquals(item))
            throw new IllegalArgumentException("given item different from this");

        if ((@Strong boolean) endDate.ref().after(new Date()))
            throw new AppException.DateException("Auction has not yet ended.");

        if (status != Status.OPEN)
            throw new AppException("Auction is already closed.");


        @Strong boolean hasWinner = !(@Strong boolean)bids.ref().isEmpty() && getTopBidPrice() >= (@Strong float) reservePrice;
        if (hasWinner) {
            status = (@MutableBottom @Local Status) Status.SOLD_VIA_AUCTION;

            @Immutable @Strong Bid winningBid = bids.ref().get(0);
            buyer = (Ref<@Mutable User>) winningBid.getUser();
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            buyer.ref().notifyWinner(item, price);
        } else {
            status = (@MutableBottom @Local Status) Status.NOT_SOLD;
        }

        seller.ref().closeOwnAuction(id, hasWinner);
        closeWatchedItemsForBidders();

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

    @StrongOp @SideEffectFree @Transactional
    public @Strong List<Bid> getAllBids() {
        if ((@Strong boolean) bids.ref().isEmpty())
            return new LinkedList<>();
        return (@Strong List<Bid>)bids.ref().subList(0, bids.ref().size() - 1); // TODO
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

    @WeakOp @SideEffectFree @Transactional
    public Date getEndDate() {
        return (@Strong Date) endDate.ref().clone();
    }

    @WeakOp @SideEffectFree
    public float getBuyNowPrice() {
        return buyNowPrice;
    }

    @StrongOp @SideEffectFree @Transactional
    public @Strong float getTopBidPrice() {
        return bids.ref().isEmpty() ? (@Strong float) initialPrice : bids.ref().get(0).getBid();
    }

    @StrongOp @SideEffectFree @Transactional
    public @Local Optional<Bid> getTopBid() {
        if ((@Strong boolean )bids.ref().isEmpty()) return Optional.empty();
        return Optional.of(bids.ref().get(0));
    }

    @Transactional @SideEffectFree
    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice;
    }

    @WeakOp @SideEffectFree
    public Ref<? extends IUser> getSeller() {
        return seller;
    }

    @WeakOp @SideEffectFree
    public @Local Optional<Ref<? extends @Mutable IUser>> getBuyer() {
        return Optional.ofNullable(buyer);
    }

    @WeakOp @SideEffectFree
    public boolean getSoldViaBuyNow() {
        return status == (@MutableBottom @Local Status) Status.SOLD_VIA_BUY_NOW;
    }

    @SideEffectFree
    public Status getStatus() {
        return status;
    }

    @Transactional @SideEffectFree
    public @Weak boolean refEquals(Ref<? extends IItem> o) {
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
        for (Bid bid : getAllBids()) {
            Ref<? extends @Mutable IUser> bidder = bid.getUser();
            bidder.ref().closeWatchedAuction(id);
        }
    }
}
