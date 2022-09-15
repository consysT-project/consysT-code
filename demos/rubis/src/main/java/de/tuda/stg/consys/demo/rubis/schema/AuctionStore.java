package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;
import java.util.function.Supplier;

public @Mixed class AuctionStore implements Serializable {
    private final Ref<@Mutable RefMap<UUID, Ref<? extends IItem>>> openAuctions;
    private final Map<Category, Ref<@Mutable RefMap<UUID, Ref<? extends IItem>>>> openAuctionsByCategory;

    public AuctionStore() {
        this.openAuctions = null;
        this.openAuctionsByCategory = null;
    }

    public AuctionStore(@Mutable Supplier<Ref<@Mutable RefMap<UUID, Ref<? extends IItem>>>> mapSupplier) {
        this.openAuctions = mapSupplier.get();
        this.openAuctionsByCategory = new HashMap<>();
        for (@Immutable Category cat : Category.values()) {
            this.openAuctionsByCategory.put(cat, mapSupplier.get());
        }
    }

    @Transactional
    @StrongOp
    public void addItem(Ref<? extends IItem> item, Category category) {
        openAuctionsByCategory.get(category).ref().put(item.ref().getId(), item);
        openAuctions.ref().put(item.ref().getId(), item);
    }

    @Transactional
    @StrongOp
    public void closeAuction(UUID id, Category category) {
        openAuctions.ref().remove(id);
        openAuctionsByCategory.get(category).ref().remove(id);
    }

    @WeakOp @SideEffectFree @Transactional
    public List<Ref<? extends IItem>> browseItems(Category category) {
        return new ArrayList<>(openAuctionsByCategory.get(category).ref().values());
    }

    @WeakOp @SideEffectFree @Transactional
    public List<Ref<? extends IItem>> getOpenAuctions() {
        return new ArrayList<>(openAuctions.ref().values());
    }
}
