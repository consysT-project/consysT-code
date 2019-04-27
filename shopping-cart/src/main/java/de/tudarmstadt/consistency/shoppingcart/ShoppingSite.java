package de.tudarmstadt.consistency.shoppingcart;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;

public class ShoppingSite implements Serializable {

    public JRef<@Weak Item> lastadded;

    public JRef<@Strong Cart> cart;

    ShoppingSite(JRef<@Strong Cart> cart) {
        this.cart = cart;
    }

    public void addToCart(JRef<@Weak Item> item) {
        lastadded = item;
        cart.invoke("add", item);
    }

    public void removeFromCart(JRef<@Weak Item> item) {
        cart.invoke("removeAll", item);
    }

    public @Strong int checkout() {
        return cart.invoke("checkout");
    }
}
