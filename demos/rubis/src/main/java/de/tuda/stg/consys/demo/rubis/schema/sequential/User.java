package de.tuda.stg.consys.demo.rubis.schema.sequential;

import de.tuda.stg.consys.demo.rubis.AppException;
import java.util.*;

public class User {
    private final UUID id;
    private final String nickname;
    private String name;
    private String password;
    private String email;
    private float rating;
    private int nRatings;
    private final List<Comment> comments = new LinkedList<>();
    private float balance;
    private final Date creationDate = new Date();
    private final Map<UUID, Item> buyerAuctions = new HashMap<>();
    private final Map<UUID, Item> buyerHistory = new HashMap<>();
    private final Map<UUID, Item> sellerAuctions = new HashMap<>();
    private final Map<UUID, Item> sellerHistory = new HashMap<>();
    private final Map<UUID, Item> sellerFailedHistory = new HashMap<>();

    public User(UUID id,
                String nickname,
                String name,
                String password,
                String email) {
        this.id = id;
        this.nickname = nickname;
        this.name = name;
        this.password = password;
        this.email = email;
    }

    public void addOwnAuction(Item item) {
        this.sellerAuctions.put(item.getId(), item);
    }

    public void closeOwnAuction(UUID id, boolean sold) {
        Item item = sellerAuctions.remove(id);
        if (item == null)
            throw new IllegalArgumentException("id not found: " + id);

        if (sold) {
            sellerHistory.put(id, item);
        } else {
            sellerFailedHistory.put(id, item);
        }
    }

    public void addWatchedAuction(Item item) {
        buyerAuctions.putIfAbsent(item.getId(), item);
    }

    public void closeWatchedAuction(UUID id) {
        buyerAuctions.remove(id);
    }

    public void addBoughtItem(Item item) {
        buyerHistory.put(item.getId(), item);
    }

    public boolean hasEnoughCredits(float price) {
        float potentialBalance = balance;

        for (var item : getOpenBuyerAuctions()) {
            Optional<Bid> bid = item.getTopBid();
            if (bid.isPresent() && this.equals(bid.get().getUser())) {
                potentialBalance -= bid.get().getBid();
            }
        }

        return potentialBalance >= price;
    }

    public List<Item> getOpenSellerAuctions() {
        return new ArrayList<>(sellerAuctions.values());
    }

    public List<Item> getOpenBuyerAuctions() {
        return new ArrayList<>(buyerAuctions.values());
    }

    public List<Item> getSellerHistory(boolean sold) {
        if (sold) return new ArrayList<>(sellerHistory.values());
        return new ArrayList<>(sellerFailedHistory.values());
    }

    public List<Item> getBuyerHistory() {
        return new ArrayList<>(buyerHistory.values());
    }

    public void addBalance(float value) {
        if (value > 0) {
            this.balance += value;
        } else {
            throw new AppException("value must be positive");
        }
    }

    public void removeBalance(float value) {
        if (value <= 0) {
            throw new AppException("value must be positive");
        } else if (balance - value < 0) {
            throw new AppException.NotEnoughCreditsException();
        } else {
            this.balance -= value;
        }
    }

    public void addRating(Comment comment) {
        if (comment.rating < 1 || comment.rating > 5) {
            throw new AppException("rating out of bounds");
        } else {
            this.rating += (comment.rating - this.rating) / ++nRatings;
            comments.add(comment);
        }
    }

    public boolean authenticate(String password) {
        return this.password.equals(password);
    }

    public float getBalance() {
        return balance;
    }

    public String getNickname() {
        return nickname;
    }

    public float getRating() {
        return rating;
    }

    public Date getCreationDate() {
        return creationDate;
    }

    public String getName() {
        return name;
    }

    public String getEmail() {
        return email;
    }

    public List<Comment> getComments() {
        return new ArrayList<>(comments);
    }

    public void setPassword(String newPassword) {
        this.password = newPassword;
    }

    public void setEmail(String newEmail) {
        this.email = newEmail;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof User && ((User)other).getNickname().equals(this.nickname);
    }

    @Override
    public String toString() {
        return "User '" + nickname + "' (" + id + ")";
    }
}
