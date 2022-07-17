package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.schema.Bid;
import de.tuda.stg.consys.demo.rubis.schema.Comment;
import de.tuda.stg.consys.demo.rubis.schema.IItem;
import de.tuda.stg.consys.demo.rubis.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Mixed class User implements Serializable, IUser {
    private final @Immutable UUID id;
    private final @Immutable String nickname;
    private String name = "";
    private @Weak String password = ""; // TODO: ?
    private @Weak String email = "";
    private float rating;
    private int nRatings;
    private final List<Comment> comments = new LinkedList<>();
    private float balance;
    private final Date creationDate = new Date();
    private final Map<UUID, Ref<@Mutable Item>> buyerAuctions = new HashMap<>();
    private final Map<UUID, Ref<@Mutable Item>> buyerHistory = new HashMap<>();
    private final Map<UUID, Ref<@Mutable Item>> sellerAuctions = new HashMap<>();
    private final Map<UUID, Ref<@Mutable Item>> sellerHistory = new HashMap<>();
    private final Map<UUID, Ref<@Mutable Item>> sellerFailedHistory = new HashMap<>();

    public User() {
        this.id = null;
        this.nickname = "";
    }

    public User(@Local UUID id, @Local String nickname, @Weak @Mutable String name, @Weak @Mutable String password,
                @Weak @Mutable String email) {
        this.id = id;
        this.nickname = nickname;
        this.name = name;
        this.password = password;
        this.email = email;
    }

    @StrongOp
    @Transactional
    public void addOwnAuction(Ref<? extends @Mutable IItem> item) {
        this.sellerAuctions.put(item.ref().getId(), toItemImpl(item));
    }

    @StrongOp
    @Transactional
    public void closeOwnAuction(UUID id, @Strong boolean sold) {
        Ref<@Mutable Item> item = sellerAuctions.remove(id);
        if (item == null)
            throw new IllegalArgumentException("id not found: " + id);

        if (sold) {
            sellerHistory.put(id, item);
        } else {
            sellerFailedHistory.put(id, item);
        }
    }

    @StrongOp
    @Transactional
    public void addWatchedAuction(Ref<? extends @Mutable IItem> item) {
        buyerAuctions.putIfAbsent(item.ref().getId(), toItemImpl(item));
    }

    @StrongOp
    public void closeWatchedAuction(UUID id) {
        buyerAuctions.remove(id);
    }

    @StrongOp
    @Transactional
    public void addBoughtItem(Ref<? extends @Mutable IItem> item) {
        buyerHistory.put(item.ref().getId(), toItemImpl(item));
    }

    @WeakOp @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.values());
    }

    @StrongOp @SideEffectFree
    // StrongOp necessary for calculating potential budget
    public List<Ref<? extends @Mutable IItem>> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.values());
    }

    @WeakOp @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getSellerHistory(boolean sold) {
        if (sold) return new ArrayList<>(sellerHistory.values());
        return new ArrayList<>(sellerFailedHistory.values());
    }

    @WeakOp @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getBuyerHistory() {
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
    public void rate(@Weak Comment comment) {
        if (comment.rating < 1 || comment.rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (comment.rating - this.rating) / ++nRatings;
            comments.add(comment);
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
    public void notifyWinner(Ref<? extends IItem> item, float price) {
        // send email
    }

    @Transactional @SideEffectFree
    public @Local boolean refEquals(Ref<? extends IUser> other) {
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

    @StrongOp @Transactional @SideEffectFree
    public @Strong boolean hasEnoughCredits(@Strong float price) {
        @Strong float potentialBalance = balance;

        for (var item : getOpenBuyerAuctions()) {
            @Immutable @Strong Optional<Bid> bid = (@Immutable @Strong Optional<Bid>) item.ref().getTopBid(); // TODO
            if ((@Strong boolean)bid.isPresent() && (@Strong boolean)refEquals(bid.get().getUser())) {
                potentialBalance -= bid.get().getBid();
            }
        }

        return potentialBalance >= price;
    }

    private Ref<@Mutable Item> toItemImpl(Ref<? extends @Mutable IItem> item) {
        return (Ref<@Mutable Item>) item;  // TODO
    }
}
