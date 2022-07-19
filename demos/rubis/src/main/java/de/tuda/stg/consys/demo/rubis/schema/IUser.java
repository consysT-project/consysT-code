package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;
import java.util.UUID;

public interface IUser extends Serializable {
    @StrongOp
    void addOwnAuction(Ref<? extends @Mutable IItem> item);

    @StrongOp
    void closeOwnAuction(UUID id, @Strong boolean sold);

    @StrongOp
    void addWatchedAuction(Ref<? extends @Mutable IItem> item);

    @StrongOp
    void closeWatchedAuction(UUID id);
    
    @StrongOp
    void addBoughtItem(Ref<? extends @Mutable IItem> item);

    @SideEffectFree
    List<Ref<? extends @Mutable IItem>> getOpenSellerAuctions();

    @StrongOp @SideEffectFree
    // StrongOp necessary for calculating potential budget
    @Strong List<Ref<? extends @Mutable IItem>> getOpenBuyerAuctions();

    @SideEffectFree
    List<Ref<? extends @Mutable IItem>> getSellerHistory(boolean sold);

    @SideEffectFree
    List<Ref<? extends @Mutable IItem>> getBuyerHistory();

    @SideEffectFree
    // If this is WeakOp you could log in with an outdated password. Security concern?
    boolean authenticate(String password);

    @StrongOp // StrongOp necessary? User should be able to use new password immediately
    void changePassword(String oldPassword, @Mutable @Weak String newPassword);

    @StrongOp // StrongOp necessary? User should be able to use new address immediately
    void changeEmail(@Mutable @Weak String newEmail, String password);

    void changeRealName(@Mutable @Weak String name);

    @StrongOp
    void addBalance(@Strong float value);

    @StrongOp
    void removeBalance(@Strong float value);

    @StrongOp @SideEffectFree
    @Strong float getBalance();

    void rate(@Weak Comment comment);

    @SideEffectFree
    @Local String getNickname();

    @WeakOp @SideEffectFree
    float getRating();

    void notifyWinner(Ref<? extends IItem> item, float price);

    @Transactional @SideEffectFree
    @Local boolean refEquals(Ref<? extends IUser> other);

    @SideEffectFree
    String toString();

    @SideEffectFree @StrongOp
    @Strong boolean hasEnoughCredits(@Strong float price);
}
