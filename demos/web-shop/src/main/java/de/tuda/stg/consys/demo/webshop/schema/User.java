package de.tuda.stg.consys.demo.webshop.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Mixed class User implements Serializable {

    private int money = 1000;

    public User() {}
    public User(@Strong int money) {
        this.money = money;
    }

    @StrongOp @Transactional
    public boolean buyProduct(Ref<@Mutable MyProduct> product, @Strong int amount) {
        if (amount <= product.ref().getQuantity() && getMoney() >= amount * product.ref().getPrice()) {
            product.ref().reduceQuantity(amount);
            reduceMoney(amount * product.ref().getPrice());
            return true;
        } else {
            return false;
        }
    }

    @StrongOp
    private void reduceMoney(@Strong int amount) {
        this.money -= amount;
    }

    @StrongOp @SideEffectFree
    public @Mutable @Strong int getMoney() {
        return this.money;
    }

    @WeakOp @SideEffectFree
    public String toString() {
        return "Money: " + money + "\n";
    }
}
