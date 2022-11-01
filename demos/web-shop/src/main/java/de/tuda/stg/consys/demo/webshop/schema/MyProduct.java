package de.tuda.stg.consys.demo.webshop.schema;

import java.io.Serializable;

public class MyProduct implements Serializable {
    private int quantity;

    public MyProduct(int quantity) {
        this.quantity = quantity;
    }

    public int getQuantity() {
        return this.quantity;
    }

    public void reduceQuantity(int amount) {
        this.quantity -= amount;
    }


}

