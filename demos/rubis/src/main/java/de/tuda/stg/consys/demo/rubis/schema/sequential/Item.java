package de.tuda.stg.consys.demo.rubis.schema.sequential;

import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.demo.rubis.schema.ItemStatus;

import java.util.*;

@SuppressWarnings({"consistency"})
public class Item {
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
    private final User seller;
    private User buyer;
    private final List<Bid> bids;
    private ItemStatus status = ItemStatus.OPEN;

    public Item(UUID id,
                String name,
                String description,
                float reservePrice,
                float initialPrice,
                float buyNowPrice,
                Date startDate,
                Date endDate,
                Category category,
                User seller) {
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
        this.buyer = null;
    }

    public boolean placeBid(Bid bid) {
        if (seller.equals(bid.getUser()))
            throw new AppException("You cannot bid on your own items.");

        if (endDate.before(new Date()))
            throw new AppException.DateException("Auction has already ended.");

        if (status != ItemStatus.OPEN)
            throw new AppException("Item is not available anymore.");

        if (!bid.getUser().hasEnoughCredits(bid.getBid()))
            throw new AppException.NotEnoughCreditsException();

        if (bid.getBid() <= getTopBidPrice())
            throw new AppException("Minimum necessary bid amount (" + getTopBidPrice() + ") not met with bid (" +
                    bid.getBid() + ")");

        bids.add(0, bid);
        nBids++;

        return bid.getBid() >= reservePrice;
    }

    public float buyNow(User buyer) {
        if (status != ItemStatus.OPEN)
            throw new AppException("Buy-Now is disabled, since item is not available anymore.");

        if (!bids.isEmpty() && getTopBidPrice() >= reservePrice)
            throw new AppException("Buy-Now is disabled, since reserve price is already met.");

        if (seller.equals(buyer))
            throw new AppException("You cannot buy your own items.");

        if (!buyer.hasEnoughCredits(buyNowPrice))
            throw new AppException.NotEnoughCreditsException();

        setEndDateToNow();
        this.buyer = buyer;
        status = ItemStatus.SOLD_VIA_BUY_NOW;

        buyer.removeBalance(buyNowPrice);
        seller.addBalance(buyNowPrice);

        buyer.addBoughtItem(this);
        seller.closeOwnAuction(id, true);
        closeWatchedItemsForBidders();

        return buyNowPrice;
    }

    public void setEndDateToNow() {
        endDate = new Date();
    }

    public boolean closeAuction() {
        if (new Date().before(endDate))
            throw new AppException.DateException("Auction has not yet ended.");

        if (status != ItemStatus.OPEN)
            throw new AppException("Auction is already closed.");

        boolean hasWinner = !bids.isEmpty() && getTopBidPrice() >= reservePrice;
        if (hasWinner) {
            Bid winningBid = bids.get(0);
            User buyer = winningBid.getUser();
            float price = winningBid.getBid();

            buyer.removeBalance(price);
            seller.addBalance(price);

            buyer.addBoughtItem(this);

            status = ItemStatus.SOLD_VIA_AUCTION;
            this.buyer = buyer;
        } else {
            status = ItemStatus.NOT_SOLD;
        }

        seller.closeOwnAuction(id, hasWinner);
        closeWatchedItemsForBidders();

        return hasWinner;
    }

    public void closeWatchedItemsForBidders() {
        for (Bid bid : bids) {
            User bidder = bid.getUser();
            bidder.closeWatchedAuction(id);
        }
    }

    public int getNumberOfBids() {
        return nBids;
    }

    public List<Bid> getAllBids() {
        return new ArrayList<>(bids);
    }

    public float getBuyNowPrice() {
        return buyNowPrice;
    }

    public float getTopBidPrice() {
        return bids.isEmpty() ? initialPrice : bids.get(0).getBid();
    }

    public Optional<Bid> getTopBid() {
        if (bids.isEmpty()) return Optional.empty();
        return Optional.of(bids.get(0));
    }

    public boolean isReserveMet() {
        return getTopBidPrice() >= reservePrice;
    }

    public boolean wasSoldViaBuyNow() {
        return status == ItemStatus.SOLD_VIA_BUY_NOW;
    }

    public UUID getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public Category getCategory() {
        return category;
    }

    public Date getEndDate() {
        return endDate;
    }

    public User getSeller() {
        return seller;
    }

    public Optional<User> getBuyer() {
        return Optional.ofNullable(buyer);
    }

    public ItemStatus getStatus() {
        return status;
    }

    public Date getStartDate() {
        return startDate;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Item && ((Item) other).getId().equals(this.id);
    }

    @Override
    public String toString() {
        return "Item '" + name + "' (" + id + ")";
    }
}
