package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
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

public @Weak class User implements Serializable, IUser {
    private final @Immutable UUID id;
    private final @Immutable String nickname;
    private String name = "";
    private @Weak String password = ""; // TODO: ?
    private @Weak String email = "";
    private float rating;
    private int nRatings;
    private final List<Comment> comments = new LinkedList<>();
    private Ref<@Strong @Mutable NumberBox<@Mutable @Strong Float>> balance;
    private final Date creationDate = new Date();
    private final Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> buyerAuctions;
    private final Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> buyerHistory;
    private final Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerAuctions;
    private final Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerHistory;
    private final Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerFailedHistory;

    public User(@Local UUID id, @Local String nickname, @Weak @Mutable String name, @Weak @Mutable String password,
                @Weak @Mutable String email,
                Ref<@Mutable NumberBox<@Mutable @Strong Float>> balance,
                Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> buyerAuctions,
                Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> buyerHistory,
                Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerAuctions,
                Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerHistory,
                Ref<@Mutable RefMap<UUID, Ref<@Mutable Item>>> sellerFailedHistory) {
        this.id = id;
        this.nickname = nickname;
        this.name = name;
        this.password = password;
        this.email = email;
        this.balance = balance;
        this.buyerAuctions = buyerAuctions;
        this.buyerHistory = buyerHistory;
        this.sellerAuctions = sellerAuctions;
        this.sellerHistory = sellerHistory;
        this.sellerFailedHistory = sellerFailedHistory;
    }

    @Transactional
    public void addOwnAuction(Ref<? extends @Mutable IItem> item) {
        this.sellerAuctions.ref().put(item.ref().getId(), toItemImpl(item));
    }

    @Transactional
    public void closeOwnAuction(UUID id, @Strong boolean sold) {
        Ref<@Mutable Item> item = sellerAuctions.ref().remove(id);
        if (item == null)
            throw new IllegalArgumentException("id not found: " + id);

        if (sold) {
            sellerHistory.ref().put(id, item);
        } else {
            sellerFailedHistory.ref().put(id, item);
        }
    }

    @Transactional
    public void addWatchedAuction(Ref<? extends @Mutable IItem> item) {
        buyerAuctions.ref().putIfAbsent(item.ref().getId(), toItemImpl(item));
    }

    @Transactional
    public void closeWatchedAuction(UUID id) {
        buyerAuctions.ref().remove(id);
    }

    @Transactional
    public void addBoughtItem(Ref<? extends @Mutable IItem> item) {
        buyerHistory.ref().put(item.ref().getId(), toItemImpl(item));
    }

    @Transactional @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.ref().values());
    }

    @Transactional @SideEffectFree
    // StrongOp necessary for calculating potential budget
    public @Strong List<Ref<? extends @Mutable IItem>> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.ref().values());
    }

    @Transactional @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getSellerHistory(boolean sold) {
        if ((@Strong boolean) sold) return new ArrayList<>(sellerHistory.ref().values());
        return new ArrayList<>(sellerFailedHistory.ref().values());
    }

    @Transactional @SideEffectFree
    public List<Ref<? extends @Mutable IItem>> getBuyerHistory() {
        return new ArrayList<>(buyerHistory.ref().values());
    }

    @SideEffectFree
    public boolean authenticate(String password) {
        return this.password.equals(password);
    }

    public void changePassword(String oldPassword, @Mutable @Weak String newPassword) {
        if (authenticate(oldPassword)) {
            this.password = newPassword;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    public void changeEmail(@Mutable @Weak String newEmail, String password) {
        if (authenticate(password)) {
            this.email = newEmail;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    public void changeRealName(@Mutable @Weak String name) {
        this.name = name;
    }

    @Transactional
    public void addBalance(@Strong float value) {
        if (value > 0) {
            balance.ref().set(balance.ref().floatValue() + value);
        } else {
            throw new AppException("value must be positive");
        }
    }

    @Transactional
    public void removeBalance(@Strong float value) {
        if (value <= 0) {
            throw new AppException("value must be positive");
        } else if (balance.ref().floatValue() - value < 0) {
            throw new AppException.NotEnoughCreditsException();
        } else {
            balance.ref().set(balance.ref().floatValue() - value);
        }
    }

    @Transactional @SideEffectFree
    public @Strong float getBalance() {
        return balance.ref().floatValue();
    }

    public void rate(@Weak Comment comment) {
        if (comment.rating < 1 || comment.rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (comment.rating - this.rating) / ++nRatings;
            comments.add(comment);
        }
    }

    @SideEffectFree
    public @Local String getNickname() { // TODO
        return (@Local String) nickname;
    }

    @SideEffectFree
    public float getRating() {
        return rating;
    }

    public void notifyWinner(Ref<? extends IItem> item, float price) {
        // send email
    }

    @Transactional @SideEffectFree
    public @Local boolean refEquals(Ref<? extends IUser> other) { // TODO
        return (@Local boolean) other.ref().getNickname().equals(this.nickname);
    }

    @SideEffectFree
    public String toString() {
        return "User '" + nickname + "' | id: " + id +
                " | name: " + name +
                " | password: " + password +
                " | email: " + email +
                " | rating: " + rating +
                " | balance: " + balance +
                " | since: " + creationDate;
    }

    @Transactional @SideEffectFree
    public @Strong boolean hasEnoughCredits(@Strong float price) {
        @Strong float potentialBalance = balance.ref().floatValue();

        for (var item : getOpenBuyerAuctions()) {
            @Immutable @Strong Optional<Bid> bid = (@Immutable @Strong Optional<Bid>) item.ref().getTopBid();
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
