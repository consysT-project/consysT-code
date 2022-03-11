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
    private final List<Tuple2<UUID, Ref<Item>>> openAuctions;
    private final Map<Category, @Mutable List<Tuple2<UUID, Ref<Item>>>> openAuctionsByCategory;

    public AuctionStore() {
        this.openAuctions = new LinkedList<>();
        this.openAuctionsByCategory = new HashMap<>();
    }

    @StrongOp
    public void addItem(Ref<Item> item, Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new LinkedList<>());
        }
        openAuctionsByCategory.get(category).add(new Tuple2<>(item.ref().getId(), item));
        openAuctions.add(new Tuple2<>(item.ref().getId(), item));
    }

    @Transactional
    @StrongOp
    public void closeAuction(UUID id, Category category) {
        openAuctions.removeIf(i -> i._1.equals(id));
        openAuctionsByCategory.get(category).removeIf(i -> i._1.equals(id));
    }

    @WeakOp
    public List<Ref<Item>> browseItems(Category category) {
        if (!openAuctionsByCategory.containsKey(category)) {
            openAuctionsByCategory.put(category, new ArrayList<>());
        }
        return openAuctionsByCategory.get(category).stream().map(t -> t._2).collect(Collectors.toList());
    }

    @WeakOp
    public List<Ref<Item>> getOpenAuctions() {
        return openAuctions.stream().map(t -> t._2).collect(Collectors.toList());
    }
}
