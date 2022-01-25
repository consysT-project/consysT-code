package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.*;

public class Rubis implements Serializable {
    private List<Ref<User>> users;
    private Map<Category, List<Ref<Item>>> openAuctionsByCategory;
    private List<Ref<Item>> openAuctions; // sort by end date?
    public List<Ref<Bid>> bids;

    public Rubis() {
        this.users = new ArrayList<>();
        this.openAuctionsByCategory = new HashMap<>();
        this.openAuctions = new LinkedList<>();
        this.bids = new ArrayList<>();
    }

    public void addUser(Ref<User> user) {
        users.add(user);
    }

    public void addItem(Ref<Item> item, Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new ArrayList<>());
        }
        openAuctionsByCategory.get(category).add(item);
        openAuctions.add(item);
    }

    public List<Ref<Item>> browseItems(Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new ArrayList<>());
        }
        return openAuctionsByCategory.get(category);
    }

    public List<Ref<Item>> getOpenAuctions() {
        return openAuctions;
    }

    public void closeAuction(String name, Category category) {
        openAuctions.removeIf(i -> i.ref().getName().equals(name));
        openAuctionsByCategory.get(category).removeIf(i -> i.ref().getName().equals(name));
    }
}
