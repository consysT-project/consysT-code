package de.tudarmstadt.consistency.shoppingcart;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Objects;

import static de.tudarmstadt.consistency.shoppingcart.Replicas.*;

public class Demo implements Serializable {

    public static void main(String... args) throws Exception {
        example1();
    }

    public static void example1() throws Exception {
        JRef<@Strong Cart> strongCart = replicaSystem1.replicate("crt", new Cart(), JConsistencyLevel.STRONG);

        JRef<@Weak ShoppingSite> weakSite = replicaSystem1.replicate("site", new ShoppingSite(strongCart), JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef1 = replicaSystem1.ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef2 = replicaSystem2.ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);

        JRef<@Weak ShoppingSite> weakSiteRef3 = replicaSystem3.ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef4 = replicaSystem4.ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);


        weakSiteRef1.invoke("addToCart", "item1");
        weakSite.invoke("addToCart", "item2");
        weakSite.invoke("removeFromCart", "item1");
        weakSiteRef2.invoke("addToCart", "item3");
        //weakSiteRef3.invoke("addToCart", "item4");
        //weakSiteRef4.invoke("addToCart", "item5");


        System.out.println("Cart: lastadded " + strongCart.getField("lastadded"));
        System.out.println("WeakSRef1: lastadded " + weakSiteRef1.getField("lastadded"));
        System.out.println("WeakSRef2: lastadded " + weakSiteRef2.getField("lastadded"));
        System.out.println("res " + weakSite.invoke("checkout"));


        replicaSystem1.close();
        replicaSystem2.close();
    }
}
