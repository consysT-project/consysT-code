package de.tuda.stg.consys.demo.webshop.schema;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class User implements Serializable {

    public boolean buyProduct(Ref<@Weak MyProduct> product, int amount) {
        if (amount <= product.ref().getQuantity()) {
            product.ref().reduceQuantity(amount);
            return true;
        } else {
            return false;
        }
    }
}
