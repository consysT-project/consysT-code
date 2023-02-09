package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;
import java.util.UUID;

public interface IUser extends Serializable {
    @StrongOp @Transactional
    void addOwnAuction(Ref<? extends @Mutable IItem> item);

    @StrongOp @Transactional
    void closeOwnAuction(UUID id, @Strong boolean sold);

    @StrongOp @Transactional
    void addWatchedAuction(Ref<? extends @Mutable IItem> item);

    @StrongOp @Transactional
    void closeWatchedAuction(UUID id);
    
    @StrongOp @Transactional
    void addBoughtItem(Ref<? extends @Mutable IItem> item);

    @SideEffectFree @Transactional
    List<Ref<? extends @Mutable IItem>> getOpenSellerAuctions();

    @StrongOp @SideEffectFree @Transactional
    // StrongOp necessary for calculating potential budget
    @Strong List<Ref<? extends @Mutable IItem>> getOpenBuyerAuctions();

    @SideEffectFree @Transactional
    List<Ref<? extends @Mutable IItem>> getSellerHistory(boolean sold);

    @SideEffectFree @Transactional
    List<Ref<? extends @Mutable IItem>> getBuyerHistory();

    @SideEffectFree @Transactional
    // If this is WeakOp you could log in with an outdated password. Security concern?
    boolean authenticate(@ThisConsistent String password);

    @StrongOp @Transactional
    void changePassword(@Mutable @Weak String newPassword);

    @StrongOp @Transactional
    void changeEmail(@Mutable @Weak String newEmail);

    @Transactional
    void changeRealName(@Mutable @Weak String name);

    @StrongOp @Transactional
    void addBalance(@Strong float value);

    @StrongOp @Transactional
    void removeBalance(@Strong float value);

    @StrongOp @SideEffectFree @Transactional
    @Strong float getBalance();

    @Transactional
    void rate(@Weak Comment comment);

    @SideEffectFree @Transactional
    @ThisConsistent String getNickname();

    @WeakOp @SideEffectFree @Transactional
    float getRating();

    @Transactional
    void notifyWinner(Ref<? extends IItem> item, float price);

    @SideEffectFree @Transactional
    @ThisConsistent boolean refEquals(Ref<? extends IUser> other);

    @SideEffectFree @Transactional
    String toString();

    @StrongOp @SideEffectFree @Transactional
    @Strong boolean hasEnoughCredits(@Strong float price);
}
