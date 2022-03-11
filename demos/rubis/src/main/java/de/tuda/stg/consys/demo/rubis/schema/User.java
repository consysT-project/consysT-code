package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

public @Mixed class User implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable String nickname;
    private String name;
    private @Weak String password; // TODO: ?
    private @Weak String email;
    private float rating;
    private int nRatings;
    private float balance;
    private final Date creationDate;
    private final Map<UUID, Ref<Item>> buyerAuctions;
    private final Map<UUID, Ref<Item>> buyerHistory;
    private final Map<UUID, Ref<Item>> sellerAuctions;
    private final Map<UUID, Ref<Item>> sellerHistory;
    private final Map<UUID, Ref<Item>> sellerFailedHistory;

    public User(@Local UUID id, @Local String nickname, @Weak @Mutable String name, @Weak @Mutable String password,
                @Weak @Mutable String email) {
        this.id = id;
        this.nickname = nickname;
        this.name = name;
        this.password = password;
        this.email = email;
        this.creationDate = new Date();
        this.buyerAuctions = new HashMap<>();
        this.buyerHistory = new HashMap<>();
        this.sellerAuctions = new HashMap<>();
        this.sellerHistory = new HashMap<>();
        this.sellerFailedHistory = new HashMap<>();
    }

    @StrongOp
    public void addOwnAuction(Ref<Item> item) {
        this.sellerAuctions.put(item.ref().getId(), item);
    }

    @StrongOp
    @Transactional
    public void closeOwnAuction(Ref<Item> item, @Strong boolean sold) {
        sellerAuctions.remove(item.ref().getId());
        if (sold) {
            sellerHistory.put(item.ref().getId(), item);
        } else {
            sellerFailedHistory.put(item.ref().getId(), item);
        }
    }

    @StrongOp
    @Transactional
    public void addWatchedAuction(Ref<Item> item) {
        buyerAuctions.putIfAbsent(item.ref().getId(), item);
    }

    @StrongOp
    @Transactional
    public void closeWatchedAuction(Ref<Item> item, @Strong boolean bought) {
        buyerAuctions.remove(item.ref().getId());
        if (bought)
            buyerHistory.put(item.ref().getId(), item);
    }

    @WeakOp @SideEffectFree
    public List<Ref<Item>> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.values());
    }

    @StrongOp @SideEffectFree
    // StrongOp necessary for calculating potential budget
    public List<Ref<Item>> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.values());
    }

    @WeakOp @SideEffectFree
    public List<Ref<Item>> getSellerHistory(boolean sold) {
        if (sold) return new ArrayList<>(sellerHistory.values());
        return new ArrayList<>(sellerFailedHistory.values());
    }

    @WeakOp @SideEffectFree
    public List<Ref<Item>> getBuyerHistory() {
        return new ArrayList<>(buyerHistory.values());
    }

    @WeakOp @SideEffectFree
    // If this is WeakOp you could log in with an outdated password. Security concern?
    public boolean authenticate(String password) {
        return this.password.equals(password);
    }

    @StrongOp // StrongOp necessary? User should be able to use new password immediately
    public void changePassword(String oldPassword, @Mutable @Weak String newPassword) {
        if (authenticate(oldPassword)) {
            this.password = newPassword;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    @StrongOp // StrongOp necessary? User should be able to use new address immediately
    public void changeEmail(@Mutable @Weak String newEmail, String password) {
        if (authenticate(password)) {
            this.email = newEmail;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    @WeakOp
    public void changeRealName(@Mutable @Weak String name) {
        this.name = name;
    }

    @StrongOp
    public void addBalance(@Strong float value) {
        if (value > 0) {
            this.balance += value;
        } else {
            throw new AppException("value must be positive");
        }
    }

    @StrongOp
    public void removeBalance(@Strong float value) {
        if (value <= 0) {
            throw new AppException("value must be positive");
        } else if (balance - value < 0) {
            throw new AppException.NotEnoughCreditsException();
        } else {
            this.balance -= value;
        }
    }

    @StrongOp @SideEffectFree
    public @Strong float getBalance() {
        return balance;
    }

    @WeakOp
    public void rate(@Weak int rating) {
        if (rating < 1 || rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (rating - this.rating) / ++nRatings;
        }
    }

    @WeakOp @SideEffectFree
    public @Local String getNickname() {
        return nickname;
    }

    @WeakOp @SideEffectFree
    public float getRating() {
        return rating;
    }

    @WeakOp
    public void notifyWinner(Ref<Item> item, float price) {
        // send email
    }

    @Transactional @SideEffectFree
    public @Local boolean refEquals(Ref<User> other) {
        return other.ref().getNickname().equals(this.nickname);
    }

    @WeakOp @SideEffectFree
    public String toString() {
        return "User '" + nickname + "' | id: " + id +
                " | name: " + name +
                " | password: " + password +
                " | email: " + email +
                " | rating: " + rating +
                " | balance: " + balance +
                " | since: " + creationDate;
    }
}
