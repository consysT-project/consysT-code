package de.tuda.stg.consys.demo.webshop.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;

public @Mixed class User implements Serializable, Triggerable {

    private int money = 1000;
    private String name = "";

    // Test "onTrigger" violations
    // 1. ref() access
    //private Ref<Object> objectRef;
    // 2. no write
    //int testField;

    public User() {}
    public User(@Weak String name, @Strong int money) {
        this.name = name;
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
        return "Money:  " + money + "\n";
    }

    @StrongOp
    public void setBalance(@Strong int money) {
        this.money = money;
    }

    @Override
    public void onTrigger() {
        // 1. ref() access
        //objectRef.ref().toString();
        //this.objectRef.ref().toString();

        // 2. no write
        //testField = 10;
        //this.testField = 10;

        // 3. Call only @SideEffectFree methods
        //reduceMoney(20);
        //this.reduceMoney(20);

        //int money = getMoney();
        //this.getMoney();
        if (money < 800) {
            System.out.println("\u001B[33m [USER WARNING]: Balance is less than 800. \u001B[0m");
        }
    }
}
