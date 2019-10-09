package de.tuda.stg.consys.shoppingcart;

import java.io.Serializable;

public class Item implements Serializable {
    public String name;
    public int price;

    public Item(String name, int price) {
        this.name = name;
        this.price = price;
    }

    public void setPrice(int price) {
        this.price = price;
    }

    @Override
    public String toString(){
        return name;
    }
}
