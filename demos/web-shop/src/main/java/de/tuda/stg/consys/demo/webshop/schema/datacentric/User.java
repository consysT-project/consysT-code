package de.tuda.stg.consys.demo.webshop.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public class User implements Serializable, Triggerable {

    private int money = 1000;

    public User() {}
    public User(int money) {
        this.money = money;
    }

    public boolean buyProduct(Ref<@Strong MyProduct> product, int amount) {
        if (amount <= product.ref().getQuantity() && getMoney() >= amount * product.ref().getPrice()) {
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

    public int getMoney() {
        return this.money;
    }

    public String toString() {
        return "Money: " + money + "\n";
    }

    @Override
    public void onTrigger() {
        if (this.money < 800) {
            System.out.println("\u001B[33m [USER WARNING]: Balance is less than 800. \u001B[0m");
        }
    }
}
