package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
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
    private List<Ref<Item>> auctions;

    public User(UUID id, String name, String nickname, String password, String email) {
        this.id = id;
        this.name = name;
        this.nickname = nickname;
        this.password = password;
        this.email = email;
        this.creationDate = new Date();
        this.auctions = new LinkedList<>();
    }

    public void addInsertedAuction(Ref<Item> item) {
        this.auctions.add(item);
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
            System.out.println("wrong password");
        }
    }

    @StrongOp // StrongOp necessary? User should be able to use new address immediately
    public void changeEmail(String newEmail, String password) {
        if (authenticate(password)) {
            this.email = newEmail;
        } else {
            System.out.println("wrong password");
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
            System.out.println("value must be positive");
        }
    }

    @StrongOp
    public void removeBalance(float value) {
        if (value > 0) {
            this.balance -= value;
        } else {
            System.out.println("value must be positive");
        }
    }

    @WeakOp
    public float getBalance() {
        return balance;
    }

    @WeakOp
    public void rate(int rating) {
        if (rating < 0 || rating > 5) {
            System.out.println("rating out of bounds");
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

    public void notifyWinner(Ref<Item> item, float price) {
        // TODO
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
