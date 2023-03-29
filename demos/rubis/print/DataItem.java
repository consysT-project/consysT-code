public @Weak class Item implements Serializable {
    private final @Immutable UUID id;
    private final String name;
    private String description;
    private final Ref<@Strong Float> reservePrice;
    private final Ref<@Strong Float> initialPrice;
    private final Ref<@Strong Float> buyNowPrice;
    private int nBids;
    private final @Immutable Date startDate;
    private final Ref<@Strong @Mutable Date> endDate;
    private final @Immutable Category category;
    private final Ref<@Mutable User> seller;
    private Ref<@Mutable User> buyer;
    private final Ref<@Strong @Mutable List<Bid>> bids;
    private final Ref<@Strong @Mutable StatusBox> status;


    @Transactional
    public boolean placeBid(Bid bid) {
        if (seller.ref().refEquals(bid.getUser()))
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
        this.buyer = buyer;
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

        @Strong boolean hasWinner = !bids.ref().isEmpty() && getTopBidPrice() >= reservePrice.ref().floatValue();
        if (hasWinner) {
            @Immutable @Strong Bid winningBid = bids.ref().get(0);
            Ref<@Mutable User> buyer = winningBid.getUser();
            @Strong float price = winningBid.getBid();

            buyer.ref().removeBalance(price);
            seller.ref().addBalance(price);

            buyer.ref().addBoughtItem(item);

            status.ref().value = ItemStatus.SOLD_VIA_AUCTION;
            this.buyer = winningBid.getUser();
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
}
