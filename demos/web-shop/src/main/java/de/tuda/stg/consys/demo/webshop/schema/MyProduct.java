package de.tuda.stg.consys.demo.webshop.schema;

import de.tuda.stg.consys.checker.qual.Immutable;

import java.io.Serializable;
import java.util.UUID;

public class MyProduct implements Serializable {
    private final UUID id;
    private String name;
    private String description;
    private int price;
    private int quantity;

    public MyProduct(String name, String description, int price, int quantity) {
        this.id = UUID.randomUUID();
        this.name = name;
        this.description = description;
        this.price = price;
        this.quantity = quantity;
    }

    public UUID getId() { return id; }
    public String getName() {
        return this.name;
    }

    public String getDescription() {
        return this.description;
    }

    public int getPrice() {
        return this.price;
    }

    public int getQuantity() {
        return this.quantity;
    }

    public void reduceQuantity(int amount) {
        this.quantity -= amount;
    }


}

