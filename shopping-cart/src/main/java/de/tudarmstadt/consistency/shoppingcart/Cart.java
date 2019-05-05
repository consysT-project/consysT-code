package de.tudarmstadt.consistency.shoppingcart;

import com.sun.deploy.panel.JreDialog;
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

    //public final String[] cart = new String[100];

    public final JRef<@Weak Item>[] cart = new JRef[100];

    public JRef<@Weak Item> lastadded;

    public boolean add(JRef<@Weak Item> item) {
        for (int i = 0; i < cart.length; i++) {
            if (cart[i] == null) {
                cart[i] = item;
                lastadded = item;
                return true;
            }
        }
        return false;
    }

    public boolean removeOne(JRef<@Weak Item> item) {
        int x = -1;
        for (int i = 0; i < cart.length; i++) {
            if (cart[i].equals(item)) {
                cart[x] = null;
                return true;
            }
        }
        return false;
    }

    public boolean removeAll(JRef<@Weak Item> item) {
        boolean ret = false;
        for (int i = 0; i < cart.length; i++) {
            if (cart[i] != null && cart[i].equals(item)) {
                cart[i] = null;
                ret = true;
            }
        }
        return ret;
    }

    @Strong
    public int checkout() {
        int ret = 0;
        System.out.println("Checked out the following items:");
        for (JRef<@Weak Item> product : cart) {
            if (product != null) {
                //product.syncAll(); //Check if this is the right function at the right time
                System.out.println(product.getField("name") + ",");
                ret = ret + (int) product.getField("price");
            }
        }
        for (int i = 0; i < cart.length; i++) {
            cart[i] = null;
        }
        System.out.print("------ \n Total: " + ret + "\n");
        return ret;
    }

}
