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
}
