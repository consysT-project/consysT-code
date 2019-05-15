package de.tudarmstadt.consistency.shoppingcart;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.jrefcollections.JRefDistList;
import de.tudarmstadt.consistency.jrefcollections.JRefLinkedList;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;
import de.tudarmstadt.consistency.replobj.japi.JReplicaSystem;

import java.io.Serializable;

import static de.tudarmstadt.consistency.shoppingcart.Replicas.*;

public class Demo implements Serializable {

    public static void main(String... args) throws Exception {
        exampleList();
    }

    public static void example1() throws Exception {


        JRef<@Strong Cart> strongCart = replicaSystems[0].replicate("crt", new Cart(), JConsistencyLevel.STRONG);

        JRef<@Weak ShoppingSite> weakSite = replicaSystems[0].replicate("site", new ShoppingSite(strongCart), JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef1 = replicaSystems[0].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef2 = replicaSystems[1].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef3 = replicaSystems[2].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef4 = replicaSystems[3].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);

        JRef<@Weak Item> item1 = replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item2 = replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3 = replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3ref = replicaSystems[1].ref("item3", Item.class, JConsistencyLevel.WEAK);

        //Add items to cart from various sites (totalling 50)
        weakSiteRef1.invoke("addToCart", item1);
        weakSite.invoke("addToCart", item2);
        weakSite.invoke("removeFromCart", item1);
        weakSiteRef2.invoke("addToCart", item3);
        weakSiteRef3.invoke("addToCart", item3);
        weakSiteRef4.invoke("addToCart", item2);
        //Increase price for item3 (changes total to 60)
        item3ref.invoke("setPrice", 20);
        item3ref.sync();

        System.out.println("Cart: lastadded " + strongCart.getField("lastadded"));
        System.out.println("WeakSRef1: lastadded " + weakSiteRef1.getField("lastadded"));
        System.out.println("WeakSRef2: lastadded " + weakSiteRef2.getField("lastadded"));
        System.out.println("WeakSRef3: lastadded " + weakSiteRef3.getField("lastadded"));
        System.out.println("WeakSRef4: lastadded " + weakSiteRef4.getField("lastadded"));
        System.out.println("res " + weakSite.invoke("checkout"));


        for (JReplicaSystem rep : replicaSystems) {
            rep.close();
        }
    }

    public static void exampleList() throws Exception {
        JRef<@Strong JRefLinkedList> strongList = replicaSystems[0].replicate("list1", new JRefLinkedList(), JConsistencyLevel.STRONG);
        JRef<@Strong JRefLinkedList> strongListRef = replicaSystems[1].ref("list1", JRefLinkedList.class, JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);


        strongList.invoke("append", item1);
        strongList.invoke("append", item2);

        strongListRef.invoke("append", item3);
        strongListRef.invoke("append", item4);

        System.out.println("Strong List index 0:" + strongList.invoke("get",0));
        System.out.println("Strong List Ref index 0:" + strongListRef.invoke("get",0));
        System.out.println("Strong List Ref index 1:" + strongListRef.invoke("get",1));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));
        //strongListRef.sync();
        System.out.println("Strong List Ref index 0:" + strongListRef.invoke("get",0));
        System.out.println("Strong List Ref index 1:" + strongListRef.invoke("get",1));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));

        strongList.invoke("insert",4,item1);
        System.out.println("Strong List Ref index 3:" + strongListRef.invoke("get",3));
        System.out.println("Strong List Ref index 4:" + strongListRef.invoke("get",4));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));

        for (JReplicaSystem rep : replicaSystems) {
            rep.close();
        }
    }
}
