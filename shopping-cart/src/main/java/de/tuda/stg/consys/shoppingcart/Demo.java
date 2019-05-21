package de.tuda.stg.consys.shoppingcart;


import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.DistNode;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.jrefcollections.JRefHashMap;
import de.tuda.stg.consys.jrefcollections.JRefLinkedList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

public class Demo implements Serializable {

    public static void main(String... args) throws Exception {
        DistListExample2();

    }

    public static void example1() throws Exception {


        JRef<@Strong Cart> strongCart = Replicas.replicaSystems[0].replicate("crt", new Cart(), JConsistencyLevel.STRONG);

        JRef<@Weak ShoppingSite> weakSite = Replicas.replicaSystems[0].replicate("site", new ShoppingSite(strongCart), JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef1 = Replicas.replicaSystems[0].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef2 = Replicas.replicaSystems[1].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef3 = Replicas.replicaSystems[2].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef4 = Replicas.replicaSystems[3].ref("site", ShoppingSite.class, JConsistencyLevel.WEAK);

        JRef<@Weak Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3ref = Replicas.replicaSystems[1].ref("item3", Item.class, JConsistencyLevel.WEAK);

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


        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    public static void exampleList() throws Exception {
        JRef<@Strong JRefLinkedList> strongList = Replicas.replicaSystems[0].replicate("list1", new JRefLinkedList(), JConsistencyLevel.STRONG);
        JRef<@Strong JRefLinkedList> strongListRef = Replicas.replicaSystems[1].ref("list1", JRefLinkedList.class, JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);


        strongList.invoke("append", item1);
        strongList.invoke("append", item2);

        strongListRef.invoke("append", item3);
        strongListRef.invoke("append", item4);

        System.out.println("Strong List index 0:" + strongList.invoke("get", 0));
        System.out.println("Strong List Ref index 0:" + strongListRef.invoke("get", 0));
        System.out.println("Strong List Ref index 1:" + strongListRef.invoke("get", 1));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));
        //strongListRef.sync();
        System.out.println("Strong List Ref index 0:" + strongListRef.invoke("get", 0));
        System.out.println("Strong List Ref index 1:" + strongListRef.invoke("get", 1));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));

        strongList.invoke("insert", 4, item1);
        System.out.println("Strong List Ref index 3:" + strongListRef.invoke("get", 3));
        System.out.println("Strong List Ref index 4:" + strongListRef.invoke("get", 4));
        System.out.println("Strong List Ref count:" + strongListRef.invoke("size"));

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void mapExample1() throws Exception{
        JRef<@Strong JRefHashMap> strongMap = Replicas.replicaSystems[0].replicate("list1", new JRefHashMap(4), JConsistencyLevel.STRONG);
        JRef<@Strong JRefHashMap> strongMapRef = Replicas.replicaSystems[1].ref("list1", JRefHashMap.class, JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        strongMap.invoke("put","Key1" ,item1);
        strongMap.invoke("put","Key2", item2);
        strongMap.invoke("put", "Key3",item3);
        System.out.println(strongMap.invoke("put", "Key2",item4).toString());
        strongMap.invoke("put","Key4", item2);
        strongMap.invoke("put", "Key5",item3);
        System.out.println(strongMap.invoke("size").toString());
        strongMap.invoke("put", null, item4);
        System.out.println(strongMap.invoke("size").toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void mapExample2() throws Exception{
        JRef<@Strong JRefHashMap> strongMap = Replicas.replicaSystems[0].replicate("list1", new JRefHashMap(4), JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        strongMap.invoke("put","a" ,item1);
        strongMap.invoke("put","e", item2);
        System.out.println(strongMap.invoke("size").toString());
        System.out.println(strongMap.invoke("get", "e").toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void DistListExample1() throws Exception{
        JRef<@Strong JRefDistList> strongDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(), JConsistencyLevel.STRONG);
        JRef<@Strong JRefDistList> strongDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        JRef<@Strong DistNode> node1 = Replicas.replicaSystems[0].replicate("node1", new DistNode(item1), JConsistencyLevel.STRONG);
        JRef<@Strong DistNode> node2 = Replicas.replicaSystems[0].replicate("node2", new DistNode(item1), JConsistencyLevel.STRONG);
        JRef<@Weak DistNode> node3 = Replicas.replicaSystems[0].replicate("node3", new DistNode(item2), JConsistencyLevel.WEAK);
        JRef<@Strong DistNode> node4 = Replicas.replicaSystems[0].replicate("node4", new DistNode(item3), JConsistencyLevel.STRONG);

        strongDistList.invoke("append", node1);
        strongDistList.invoke("append", node2);
        strongDistList.invoke("append", node3);
        strongDistList.invoke("append", node4);

        System.out.println(strongDistList.invoke("size").toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void DistListExample2() throws Exception{
        JRef<@Weak JRefDistList> weakDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(), JConsistencyLevel.WEAK);
        JRef<@Weak JRefDistList> weakDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.WEAK);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        JRef<@Weak DistNode> node1 = Replicas.replicaSystems[0].replicate("node1", new DistNode(item1), JConsistencyLevel.WEAK);
        JRef<@Weak DistNode> node2 = Replicas.replicaSystems[1].replicate("node2", new DistNode(item1), JConsistencyLevel.WEAK);
        JRef<@Weak DistNode> node3 = Replicas.replicaSystems[0].replicate("node3", new DistNode(item2), JConsistencyLevel.WEAK);
        JRef<@Weak DistNode> node4 = Replicas.replicaSystems[1].replicate("node4", new DistNode(item3), JConsistencyLevel.WEAK);

        weakDistList.invoke("append", node1);
        weakDistList.invoke("append", node2);
        weakDistList.invoke("append", node3);
        weakDistList.invoke("append", node4);

        System.out.println(weakDistList.invoke("size").toString());
        System.out.println(weakDistListRef.invoke("size").toString());
        System.out.println(weakDistList.invoke("get",2).toString());
        System.out.println(weakDistList.invoke("getSeq",2).toString());
        weakDistListRef.sync();
        System.out.println(weakDistListRef.invoke("size").toString());
        System.out.println(weakDistListRef.invoke("get",3).toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }
}
