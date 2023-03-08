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
    private Option<Ref<@Mutable User>> buyer;
    private final List<Bid> bids;
    private @Mutable @Weak ItemStatus status = ItemStatus.OPEN;


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
        this.buyer = Option.apply(buyer);
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

        @Strong boolean hasWinner = !bids.isEmpty() && getTopBidPrice() >= reservePrice;
        if (hasWinner) {
            @Immutable @Strong Bid winningBid = bids.get(0);
            Ref<@Mutable User> buyer = winningBid.getUser();
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            status = ItemStatus.SOLD_VIA_AUCTION;
            this.buyer = Option.apply(buyer);
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
}
