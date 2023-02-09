package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Weak class User implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable String nickname;
    private String name;
    private String password;
    private String email;
    private float rating;
    private int nRatings;
    private final List<Comment> comments = new LinkedList<>();
    private final Ref<@Mutable @Strong NumberBox<@Mutable @Strong Float>> balance;
    private final Date creationDate = new Date();
    private final Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> buyerAuctions;
    private final Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> buyerHistory;
    private final Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerAuctions;
    private final Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerHistory;
    private final Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerFailedHistory;

    public User(@Local UUID id,
                @Local String nickname,
                @Weak @Mutable String name,
                @Weak @Mutable String password,
                @Weak @Mutable String email,
                Ref<@Mutable NumberBox<@Mutable @Strong Float>> balance,
                Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> buyerAuctions,
                Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> buyerHistory,
                Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerAuctions,
                Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerHistory,
                Ref<@Mutable Map<UUID, Ref<@Mutable Item>>> sellerFailedHistory) {
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
    public void addOwnAuction(Ref<@Mutable Item> item) {
        this.sellerAuctions.ref().put(item.ref().getId(), item);
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
    public void addWatchedAuction(Ref<@Mutable Item> item) {
        buyerAuctions.ref().putIfAbsent(item.ref().getId(), item);
    }

    @Transactional
    public void closeWatchedAuction(UUID id) {
        buyerAuctions.ref().remove(id);
    }

    @Transactional
    public void addBoughtItem(Ref<@Mutable Item> item) {
        buyerHistory.ref().put(item.ref().getId(), item);
    }

    @Transactional
    @SideEffectFree
    public @Strong boolean hasEnoughCredits(@Strong float price) {
        @Strong float potentialBalance = balance.ref().floatValue();

        for (var item : getOpenBuyerAuctions()) {
            @Immutable @Strong Optional<Bid> bid = (@Immutable @Strong Optional<Bid>) item.ref().getTopBid(); // TODO: timeout?
            if (bid.isPresent() && (@Strong boolean)refEquals(bid.get().getUser())) {
                potentialBalance -= bid.get().getBid();
            }
        }

        return potentialBalance >= price;
    }

    @Transactional
    @SideEffectFree
    public List<Ref<@Mutable Item>> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.ref().values());
    }

    @Transactional
    @SideEffectFree
    public @Strong List<Ref<@Mutable Item>> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.ref().values());
    }

    @Transactional
    @SideEffectFree
    public List<Ref<@Mutable Item>> getSellerHistory(boolean sold) {
        if ((@Strong boolean) sold) return new ArrayList<>(sellerHistory.ref().values());
        return new ArrayList<>(sellerFailedHistory.ref().values());
    }

    @Transactional
    @SideEffectFree
    public List<Ref<@Mutable Item>> getBuyerHistory() {
        return new ArrayList<>(buyerHistory.ref().values());
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

    public void addRating(@Weak Comment comment) {
        if (comment.rating < 1 || comment.rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (comment.rating - this.rating) / ++nRatings;
            comments.add(comment);
        }
    }

    @SideEffectFree
    public boolean authenticate(@Weak String password) {
        return this.password.equals(password);
    }

    @Transactional
    @SideEffectFree
    public @Strong float getBalance() {
        return balance.ref().floatValue();
    }

    @SideEffectFree
    public @Weak String getNickname() { // TODO
        return nickname;
    }

    @SideEffectFree
    public float getRating() {
        return rating;
    }

    @SideEffectFree
    public Date getCreationDate() {
        return creationDate;
    }

    @SideEffectFree
    public String getName() {
        return name;
    }

    @SideEffectFree
    public String getEmail() {
        return email;
    }

    @SideEffectFree
    public List<Comment> getComments() {
        return new ArrayList<>(comments);
    }

    public void setPassword(@Mutable @Weak String newPassword) {
        this.password = newPassword;
    }

    public void setEmail(@Mutable @Weak String newEmail) {
        this.email = newEmail;
    }

    public void setName(@Mutable @Weak String name) {
        this.name = name;
    }

    @Transactional
    @SideEffectFree
    public @Weak boolean refEquals(Ref<User> other) {
        return other.ref().getNickname().equals(this.nickname);
    }

    @Override
    @SideEffectFree
    public String toString() {
        return "User '" + nickname + "' (" + id + ")";
    }
}
