package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.*;

public class AuctionStore implements Serializable {
    private final List<Ref<User>> users;
    private final List<Ref<Item>> openAuctions;
    private final Map<Category, List<Ref<Item>>> openAuctionsByCategory;

    public AuctionStore() {
        this.users = new ArrayList<>();
        this.openAuctions = new LinkedList<>();
        this.openAuctionsByCategory = new HashMap<>();
    }

    @StrongOp
    public void addUser(Ref<User> user) {
        users.add(user);
    }

    @StrongOp
    public void addItem(Ref<Item> item, Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new LinkedList<>());
        }
        openAuctionsByCategory.get(category).add(item);
        openAuctions.add(item);
    }

    @StrongOp
    public void closeAuction(UUID id, Category category) {
        openAuctions.removeIf(i -> i.ref().getId().equals(id));
        openAuctionsByCategory.get(category).removeIf(i -> i.ref().getId().equals(id));
    }

    @WeakOp
    public List<Ref<Item>> browseItems(Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new ArrayList<>());
        }
        return openAuctionsByCategory.get(category);
    }

    @WeakOp
    public List<Ref<Item>> getOpenAuctions() {
        return openAuctions;
    }

    @WeakOp
    public Optional<Ref<User>> searchUser(String nickname) {
        return users.stream().filter(user -> user.ref().getNickname().equals(nickname)).findFirst();
    }
}
