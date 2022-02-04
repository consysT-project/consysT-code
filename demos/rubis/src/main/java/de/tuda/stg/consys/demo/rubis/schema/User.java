package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public class User implements Serializable {
    private final UUID id;
    private String name;
    private final String nickname;
    private String password;
    private String email;
    private float rating;
    private int nRatings;
    private float balance;
    private final Date creationDate;
    private final List<Ref<Item>> buyerAuctions;
    private final List<Ref<Item>> buyerHistory;
    private final List<Ref<Item>> sellerAuctions;
    private final List<Ref<Item>> sellerHistory;
    private final List<Ref<Item>> sellerFailedHistory;

    public User(UUID id, String name, String nickname, String password, String email) {
        this.id = id;
        this.name = name;
        this.nickname = nickname;
        this.password = password;
        this.email = email;
        this.creationDate = new Date();
        this.buyerAuctions = new LinkedList<>();
        this.buyerHistory = new LinkedList<>();
        this.sellerAuctions = new LinkedList<>();
        this.sellerHistory = new LinkedList<>();
        this.sellerFailedHistory = new LinkedList<>();
    }

    @StrongOp
    public void addOwnAuction(Ref<Item> item) {
        this.sellerAuctions.add(item);
    }

    @StrongOp
    public void closeOwnAuction(Ref<Item> item, boolean sold) {
        sellerAuctions.removeIf(i -> item.ref().getId().equals(i.ref().getId()));
        if (sold) {
            sellerHistory.add(item);
        } else {
            sellerFailedHistory.add(item);
        }
    }

    @StrongOp
    public void addWatchedAuction(Ref<Item> item) {
        buyerAuctions.removeIf(x -> item.ref().getId().equals(x.ref().getId()));
        buyerAuctions.add(0, item);
    }

    @StrongOp
    public void closeWatchedAuction(Ref<Item> item) {
        buyerAuctions.removeIf(i -> item.ref().getId().equals(i.ref().getId()));
        buyerHistory.add(item);
    }

    @WeakOp
    public List<Ref<Item>> getOpenSellerAuctions() {
        return sellerAuctions;
    }

    @WeakOp
    public List<Ref<Item>> getOpenBuyerAuctions() {
        return buyerAuctions;
    }

    @WeakOp
    public List<Ref<Item>> getSellerHistory(boolean sold) {
        return sold ? sellerHistory : sellerFailedHistory;
    }

    @WeakOp
    public List<Ref<Item>> getBuyerHistory() {
        return buyerHistory;
    }

    @WeakOp // If this is WeakOp you could log in with an outdated password. Security concern?
    public boolean authenticate(String password) {
        return this.password.equals(password);
    }

    @StrongOp // StrongOp necessary? User should be able to use new password immediately
    public void changePassword(String oldPassword, String newPassword) {
        if (authenticate(oldPassword)) {
            this.password = newPassword;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    @StrongOp // StrongOp necessary? User should be able to use new address immediately
    public void changeEmail(String newEmail, String password) {
        if (authenticate(password)) {
            this.email = newEmail;
        } else {
            throw new AppException("Wrong credentials.");
        }
    }

    @WeakOp
    public void changeRealName(String name) {
        this.name = name;
    }

    @StrongOp
    public void addBalance(float value) {
        if (value > 0) {
            this.balance += value;
        } else {
            throw new AppException("value must be positive");
        }
    }

    @StrongOp
    public void removeBalance(float value) {
        if (value <= 0) {
            throw new AppException("value must be positive");
        } else if (balance - value < 0) {
            throw new AppException.NotEnoughCreditsException();
        } else {
            this.balance -= value;
        }
    }

    @WeakOp
    public float getBalance() {
        return balance;
    }

    @WeakOp
    public void rate(int rating) {
        if (rating < 1 || rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (rating - this.rating) / ++nRatings;
        }
    }

    @WeakOp
    public String getNickname() {
        return nickname;
    }

    @WeakOp
    public float getRating() {
        return rating;
    }

    @WeakOp
    public void notifyWinner(Ref<Item> item, float price) {
        // send email
    }

    @WeakOp
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
