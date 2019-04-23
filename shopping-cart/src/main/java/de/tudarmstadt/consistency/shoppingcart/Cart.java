package de.tudarmstadt.consistency.shoppingcart;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import java.io.Serializable;

/**
 * Created on 20.04.19.
 *
 * @author martin edlund
 */
public class Cart implements Serializable {

    public final String[] cart = new String[100];

    public String lastadded;

    public boolean add(String name) {
        for (int i = 0; i < cart.length; i++) {
            if (cart[i] == null) {
                cart[i] = name;
                lastadded = name;
                return true;
            }
        }
        return false;
    }

    public boolean removeOne(String name) {
        int x = -1;
        for (int i = 0; i < cart.length; i++) {
            if (cart[i].equals(name)) {
                cart[x] = null;
                return true;
            }
        }
        return false;
    }

    public boolean removeAll(String name) {
        boolean ret = false;
        for (int i = 0; i < cart.length; i++) {
            if (cart[i] != null && cart[i].equals(name)) {
                cart[i] = null;
                ret = true;
            }
        }
        return ret;
    }

    @Strong
    public int checkout() {
        int ret = 0;
        for (String product : cart) {
            if (product != null) {
                System.out.println("Checked out " + product);
                ret = ret + 1;
            }
        }
        for (int i = 0; i < cart.length; i++) {
            cart[i] = null;
        }
        return ret;
    }

}
