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

    @Transactional
    @StrongOp
    boolean placeBid(Bid bid);

    @Transactional
    @StrongOp
    @Strong float buyNow(Ref<? extends @Mutable IUser> buyer, Ref<? extends @Mutable IItem> item);

    @StrongOp
    void endAuctionNow();

    @Transactional
    @StrongOp
    boolean closeAuction(Ref<? extends @Mutable IItem> item);

    @WeakOp
    void setDescription(@Mutable @Weak String description);

    @WeakOp @SideEffectFree
    int getNumberOfBids();

    @StrongOp @SideEffectFree
    @Strong List<Bid> getAllBids();

    @WeakOp @SideEffectFree
    Category getCategory();

    @WeakOp @SideEffectFree
    UUID getId();

    @WeakOp @SideEffectFree
    String getName();

    @WeakOp @SideEffectFree
    Date getEndDate();

    @WeakOp @SideEffectFree
    float getBuyNowPrice();

    @StrongOp @SideEffectFree
    @Strong float getTopBidPrice();

    @StrongOp @SideEffectFree
    @Local Optional<Bid> getTopBid();

    boolean isReserveMet();

    @WeakOp @SideEffectFree
    Ref<? extends IUser> getSeller();

    @WeakOp @SideEffectFree
    @Local Optional<Ref<? extends @Mutable IUser>> getBuyer();

    @WeakOp @SideEffectFree
    boolean getSoldViaBuyNow();

    @WeakOp @SideEffectFree
    ItemStatus getStatus();

    @Transactional @SideEffectFree
    boolean refEquals(Ref<? extends IItem> o);

    @WeakOp @SideEffectFree @Transactional
    String toString();

    void closeWatchedItemsForBidders();
}
