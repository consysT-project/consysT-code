package de.tuda.stg.consys.demo.webshop.schema;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class User implements Serializable {

    int money = 1000;

    public User() {}
    public User(int money) {
        this.money = money;
    }

    public boolean buyProduct(Ref<@Weak MyProduct> product, int amount) {
        if (amount <= product.ref().getQuantity() && money >= amount * product.ref().getPrice()) {
            product.ref().reduceQuantity(amount);
            reduceMoney(amount * product.ref().getPrice());
            return true;
        } else {
            return false;
        }
    }

    private void reduceMoney(int amount) {
        this.money -= amount;
    }

    public String toString() {
        return "Money: " + money + "\n";
    }
}
