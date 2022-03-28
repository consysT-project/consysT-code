package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import scala.Tuple2;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

public @Mixed class AuctionStore implements Serializable {
    private final Map<UUID, Ref<Item>> openAuctions;
    private final Map<Category, @Mutable Map<UUID, Ref<Item>>> openAuctionsByCategory;

    public AuctionStore() {
        this.openAuctions = new HashMap<>();
        this.openAuctionsByCategory = new HashMap<>();
        for (@Immutable Category cat : Category.values()) {
            this.openAuctionsByCategory.put(cat, new HashMap<>());
        }
    }

    @Transactional
    @StrongOp
    public void addItem(Ref<Item> item, Category category) {
        openAuctionsByCategory.get(category).put(item.ref().getId(), item);
        openAuctions.put(item.ref().getId(), item);
    }

    @Transactional
    @StrongOp
    public void closeAuction(UUID id, Category category) {
        openAuctions.remove(id);
        openAuctionsByCategory.get(category).remove(id);
    }

    @WeakOp
    public List<Ref<Item>> browseItems(Category category) {
        return new ArrayList<>(openAuctionsByCategory.get(category).values());
    }

    @WeakOp
    public List<Ref<Item>> getOpenAuctions() {
        return new ArrayList<>(openAuctions.values());
    }
}
