package de.tuda.stg.consys.shoppingcart;


import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
/*
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.jrefcollections.JRefHashMap;
import de.tuda.stg.consys.jrefcollections.JRefLinkedList;
 */
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

public class Demo implements Serializable {

    public static void main(String... args) throws Exception {
        example1();

    }

    public static void example1() throws Exception {


        JRef<@Strong Cart> strongCart = Replicas.replicaSystems[0].replicate("crt", new Cart(), JConsistencyLevels.STRONG);

        JRef<@Weak ShoppingSite> weakSite = Replicas.replicaSystems[0].replicate("site", new ShoppingSite(strongCart), JConsistencyLevels.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef1 = Replicas.replicaSystems[0].lookup("site", ShoppingSite.class, JConsistencyLevels.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef2 = Replicas.replicaSystems[1].lookup("site", ShoppingSite.class, JConsistencyLevels.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef3 = Replicas.replicaSystems[2].lookup("site", ShoppingSite.class, JConsistencyLevels.WEAK);
        JRef<@Weak ShoppingSite> weakSiteRef4 = Replicas.replicaSystems[3].lookup("site", ShoppingSite.class, JConsistencyLevels.WEAK);

        JRef<@Weak Item> item1 = Replicas.replicaSystems[0].replicate(new Item("item1", 5), JConsistencyLevels.WEAK);
        JRef<@Weak Item> item2 = Replicas.replicaSystems[0].replicate(new Item("item2", 10), JConsistencyLevels.WEAK);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevels.WEAK);
        JRef<@Weak Item> item3ref = Replicas.replicaSystems[1].lookup("item3", Item.class, JConsistencyLevels.WEAK);

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
/*
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
        JRef<@Strong JRefDistList> strongDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(JConsistencyLevel.STRONG), JConsistencyLevel.STRONG);
        JRef<@Strong JRefDistList> strongDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.STRONG);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        strongDistList.invoke("append", item1, Replicas.replicaSystems[0]);
        strongDistList.invoke("append", item2, Replicas.replicaSystems[0]);
        strongDistList.invoke("append", item3, Replicas.replicaSystems[0]);
        strongDistList.invoke("append", item4, Replicas.replicaSystems[0]);

        System.out.println(strongDistList.invoke("size").toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void DistListExample2() throws Exception{
        JRef<@Weak JRefDistList> weakDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
        JRef<@Weak JRefDistList> weakDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.WEAK);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);


        weakDistList.invoke("append", item1, Replicas.replicaSystems[0]);
        weakDistList.invoke("append", item2, Replicas.replicaSystems[0]);
        weakDistList.invoke("append", item3, Replicas.replicaSystems[0]);
        weakDistList.invoke("append", item4, Replicas.replicaSystems[0]);

        System.out.println(weakDistList.invoke("size").toString());
        System.out.println(weakDistListRef.invoke("size").toString());
        System.out.println(weakDistList.invoke("getIndex",2).toString());
        System.out.println(weakDistList.invoke("getIndex",2).toString());
        weakDistListRef.syncAll();
        System.out.println("After Sync");
        System.out.println(weakDistListRef.invoke("size").toString());
        System.out.println(weakDistListRef.invoke("getIndex",3).toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void DistListExample3() throws Exception{
        JRef<@Weak JRefDistList> weakDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
        JRef<@Weak JRefDistList> weakDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.WEAK);

        JRef<@Strong Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.STRONG);
        JRef<@Strong Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.STRONG);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[0].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);


        weakDistList.invoke("append", item1, Replicas.replicaSystems[0]);

        System.out.println(weakDistList.invoke("size").toString());
        System.out.println(weakDistList.invoke("removeIndex", 0, true).toString());
        System.out.println(weakDistList.invoke("size").toString());
        System.out.println(weakDistList.invoke("insert",0,item1,Replicas.replicaSystems[0], true).toString());
        System.out.println(weakDistList.invoke("size").toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void DistListExample4() throws Exception{
        JRef<@Weak JRefDistList> weakDistList = Replicas.replicaSystems[0].replicate("list1", new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
        JRef<@Weak JRefDistList> weakDistListRef = Replicas.replicaSystems[1].ref("list1", JRefDistList.class, JConsistencyLevel.WEAK);

        JRef<@Weak Item> item1 = Replicas.replicaSystems[0].replicate("item1", new Item("item1", 5), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item2 = Replicas.replicaSystems[0].replicate("item2", new Item("item2", 10), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item3 = Replicas.replicaSystems[1].replicate("item3", new Item("item3", 15), JConsistencyLevel.WEAK);
        JRef<@Weak Item> item4 = Replicas.replicaSystems[0].replicate("item4", new Item("item3", 20), JConsistencyLevel.WEAK);

        JRef<@Weak Item> item1_copy  = Replicas.replicaSystems[1].ref("item1", Item.class, JConsistencyLevel.WEAK);

        //TODO: Find more instances of error.

        //How to compare if two JRefs reference the same thing?
        System.out.println(item1.toString().equals(item1_copy.toString()));
        System.out.println(item1.hashCode()==item1_copy.hashCode());
        System.out.println(item1.equals(item1_copy));

        weakDistList.invoke("append", item1, Replicas.replicaSystems[0]);
        weakDistList.invoke("append", item1, Replicas.replicaSystems[0]);


        weakDistListRef.sync();
        System.out.println(weakDistList.invoke("size",true).toString());
        System.out.println(weakDistListRef.invoke("size",true).toString());


        weakDistListRef.invoke("append", item3, Replicas.replicaSystems[1]);


        System.out.println("--------------");

        weakDistList.invoke("insert",0,item2,Replicas.replicaSystems[0], false);

        System.out.println("--------------");

        //Why does weakDistList not sync properly?
        System.out.println(weakDistList.invoke("size",true).toString());
        System.out.println(weakDistListRef.invoke("size",true).toString());

        System.out.println("--------------");

        //Why does this crash?
        System.out.println(weakDistList.invoke("size",true).toString());

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }


    private static void minimalError() throws Exception {
        JRef<@Weak ErrorClass> baseClass = Replicas.replicaSystems[0].replicate("errorClass", new ErrorClass(), JConsistencyLevel.WEAK);
        JRef<@Weak ErrorClass> baseClassRef = Replicas.replicaSystems[1].ref("errorClass", ErrorClass.class, JConsistencyLevel.WEAK);


        baseClass.invoke("add", Replicas.replicaSystems[0]);
        baseClassRef.sync();


        JRef<@Weak ErrorSubClass> node = Replicas.replicaSystems[1].replicate(new ErrorSubClass(), JConsistencyLevel.WEAK);

        //It makes no difference if the element is added in the class itself or here.
        //baseClassRef.invoke("add", Replicas.replicaSystems[1]);
        baseClassRef.invoke("addGivenNode", node);

        //if the replicated object is synced, it does not detect the change on the reference
        baseClass.syncAll();

        //if the reference is synced, it causes an serialisation error error
        //baseClassRef.syncAll();

        //This crashes the programm when element replicated on replicaSystems[1] is being attempted to use.
        //This occurs only when the objects on the reference where synced individually

        //This does not cause a crash
        baseClass.invoke("printAndSync");
        System.out.println("---------------");
        //This prints all objects from the view of the reference correctly
        baseClassRef.invoke("printAndSync");
        System.out.println("---------------");
        //This finds the added object but crashes when trying to use it.
        baseClass.invoke("printAndSync");

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }
*/
    private static void anotherError() throws Exception {
        JRef<@Weak ErrorClass> baseClass = Replicas.replicaSystems[0].replicate("errorClass", new ErrorClass(), JConsistencyLevels.WEAK);

        System.out.println("This will be printed");
        baseClass.invoke("createInternal");
        System.out.println("This wont be printed");

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }

    private static void anotherError2() throws Exception{
        JRef<@Weak ErrorClass> baseClass = Replicas.replicaSystems[0].replicate("errorClass", new ErrorClass(), JConsistencyLevels.WEAK);

        Object[] arr = new Object[10];

        String[] strArr = {"Alpha", "Beta", "Gamma"};

        baseClass.invoke("takeArray", arr);

        //baseClass.invoke("takeStrArray", strArr);

        for (JReplicaSystem rep : Replicas.replicaSystems) {
            rep.close();
        }
    }
}
