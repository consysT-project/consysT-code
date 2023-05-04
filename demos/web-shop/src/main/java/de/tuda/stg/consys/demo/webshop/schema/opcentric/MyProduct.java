package de.tuda.stg.consys.demo.webshop.schema.opcentric;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.UUID;

public @Mixed class MyProduct implements Serializable {
    private @Immutable UUID id;
    private String name;
    private String description;
    private int price;
    private int quantity;

    public MyProduct() {}

    public MyProduct(@Local @Mutable String name, @Local @Mutable String description, @Local @Mutable int price, @Strong @Mutable int quantity) {
        this.id = UUID.randomUUID();
        this.name = name;
        this.description = description;
        this.price = price;
        this.quantity = quantity;
    }
    @WeakOp @SideEffectFree
    public UUID getId() { return this.id; }

    @WeakOp @SideEffectFree
    public String getName() {
        return this.name;
    }

    @WeakOp @SideEffectFree
    public String getDescription() {
        return this.description;
    }

    @StrongOp @SideEffectFree
    public int getPrice() {
        return this.price;
    }

    @StrongOp @SideEffectFree
    public int getQuantity() {
        return this.quantity;
    }
    @StrongOp
    public void reduceQuantity(@Strong int amount) {
        this.quantity -= amount;
    }

    public String toString() {
        return "Name: " + name + " | Description: " + description + " | Price: " + price + " | Quantity: " + quantity + "\n";
    }
    
}

