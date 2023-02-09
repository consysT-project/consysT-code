package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Mixed class User implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable String nickname;
    private String name = "";
    private @Weak String password = "";
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

    public User(@Local UUID id,
                @Local String nickname,
                @Weak @Mutable String name,
                @Weak @Mutable String password,
                @Weak @Mutable String email) {
        this.id = id;
        this.nickname = nickname;
        this.name = name;
        this.password = password;
        this.email = email;
    }

    @StrongOp
    @Transactional
    public void addOwnAuction(Ref<@Mutable Item> item) {
        this.sellerAuctions.put(item.ref().getId(), item);
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
    public void addWatchedAuction(Ref<@Mutable Item> item) {
        buyerAuctions.putIfAbsent(item.ref().getId(), item);
    }

    @StrongOp
    public void closeWatchedAuction(UUID id) {
        buyerAuctions.remove(id);
    }

    @StrongOp
    @Transactional
    public void addBoughtItem(Ref<@Mutable Item> item) {
        buyerHistory.put(item.ref().getId(), item);
    }

    @StrongOp
    @Transactional
    @SideEffectFree
    public @Strong boolean hasEnoughCredits(@Strong float price) {
        @Strong float potentialBalance = balance;

        for (var item : getOpenBuyerAuctions()) {
            @Immutable @Strong Optional<Bid> bid = item.ref().getTopBid();
            if (bid.isPresent() && refEquals(bid.get().getUser())) {
                potentialBalance -= bid.get().getBid();
            }
        }

        return potentialBalance >= price;
    }

    @SideEffectFree
    public List<Ref<@Mutable Item>> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.values());
    }

    @StrongOp
    @SideEffectFree
    public @Strong List<Ref<@Mutable Item>> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.values());
    }

    @SideEffectFree
    public List<Ref<@Mutable Item>> getSellerHistory(boolean sold) {
        if (sold) return new ArrayList<>(sellerHistory.values());
        return new ArrayList<>(sellerFailedHistory.values());
    }

    @SideEffectFree
    public List<Ref<@Mutable Item>> getBuyerHistory() {
        return new ArrayList<>(buyerHistory.values());
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

    @StrongOp
    @SideEffectFree
    public @Strong float getBalance() {
        return balance;
    }

    @SideEffectFree
    public @Local String getNickname() {
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

    @StrongOp
    public void setPassword(@Mutable @Weak String newPassword) {
        this.password = newPassword;
    }

    @StrongOp
    public void setEmail(@Mutable @Weak String newEmail) {
        this.email = newEmail;
    }

    public void setName(@Mutable @Weak String name) {
        this.name = name;
    }

    @Transactional
    @SideEffectFree
    public @Local boolean refEquals(Ref<User> other) {
        return other.ref().getNickname().equals(this.nickname);
    }

    @Override
    @SideEffectFree
    public String toString() {
        return "User '" + nickname + "' (" + id + ")";
    }
}
