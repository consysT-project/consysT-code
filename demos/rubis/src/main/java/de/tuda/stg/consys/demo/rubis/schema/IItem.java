package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

public interface IItem extends Serializable {

    @StrongOp @Transactional
    boolean placeBid(Bid bid);

    @StrongOp @Transactional
    @Strong float buyNow(Ref<? extends @Mutable IUser> buyer, Ref<? extends @Mutable IItem> item);

    @StrongOp @Transactional
    void endAuctionNow();

    @StrongOp @Transactional
    boolean closeAuction(Ref<? extends @Mutable IItem> item);

    @WeakOp @Transactional
    void setDescription(@Mutable @Weak String description);

    @WeakOp @SideEffectFree @Transactional
    int getNumberOfBids();

    @StrongOp @SideEffectFree @Transactional
    @Strong List<Bid> getAllBids();

    @WeakOp @SideEffectFree @Transactional
    Category getCategory();

    @WeakOp @SideEffectFree @Transactional
    @Weak UUID getId();

    @WeakOp @SideEffectFree @Transactional
    String getName();

    @WeakOp @SideEffectFree @Transactional
    Date getEndDate();

    @WeakOp @SideEffectFree @Transactional
    float getBuyNowPrice();

    @StrongOp @SideEffectFree @Transactional
    @Strong float getTopBidPrice();

    @StrongOp @SideEffectFree @Transactional
    @Local Optional<Bid> getTopBid();

    @Transactional
    boolean isReserveMet();

    @WeakOp @SideEffectFree @Transactional
    Ref<? extends IUser> getSeller();

    @WeakOp @SideEffectFree @Transactional
    @Local Optional<Ref<? extends @Mutable IUser>> getBuyer();

    @WeakOp @SideEffectFree @Transactional
    boolean getSoldViaBuyNow();

    @WeakOp @SideEffectFree @Transactional
    ItemStatus getStatus();

    @SideEffectFree @Transactional
    boolean refEquals(Ref<? extends IItem> o);

    @WeakOp @SideEffectFree @Transactional
    String toString();

    @Transactional
    void closeWatchedItemsForBidders();
}
