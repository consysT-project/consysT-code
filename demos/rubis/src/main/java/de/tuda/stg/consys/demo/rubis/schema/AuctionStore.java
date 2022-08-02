package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Mixed class AuctionStore implements Serializable {
    private final Map<UUID, Ref<? extends IItem>> openAuctions;
    private final Map<Category, @Mutable Map<UUID, Ref<? extends IItem>>> openAuctionsByCategory;

    public AuctionStore() {
        this.openAuctions = new HashMap<>();
        this.openAuctionsByCategory = new HashMap<>();
        for (@Immutable Category cat : Category.values()) {
            this.openAuctionsByCategory.put(cat, new HashMap<>());
        }
    }

    @Transactional
    @StrongOp
    public void addItem(Ref<? extends IItem> item, Category category) {
        openAuctionsByCategory.get(category).put(item.ref().getId(), item);
        openAuctions.put(item.ref().getId(), item);
    }

    @Transactional
    @StrongOp
    public void closeAuction(UUID id, Category category) {
        openAuctions.remove(id);
        openAuctionsByCategory.get(category).remove(id);
    }

    @WeakOp @SideEffectFree
    public List<Ref<? extends IItem>> browseItems(Category category) {
        return new ArrayList<>(openAuctionsByCategory.get(category).values());
    }

    @WeakOp @SideEffectFree
    public List<Ref<? extends IItem>> getOpenAuctions() {
        return new ArrayList<>(openAuctions.values());
    }
}
