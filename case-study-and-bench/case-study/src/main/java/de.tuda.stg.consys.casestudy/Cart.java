package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.collections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.HashMap;
import java.util.LinkedList;

public class Cart implements Serializable{

    private JRef<@Weak JRefDistList> cartContent;

    Cart(JReplicaSystem system){
        cartContent = system.replicate(new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
    }

    /*
     * Add an Item to the Cart, if the item is already in the cart, add the new count to the old count,
     * if the new count is less or equal to zero return false.
     */
    public boolean add(JRef<@Strong Product> item, int count) throws Error{

        if(count <= 0) return false;

        for(int x = 0;x < count;x++){
            cartContent.invoke("append", item);
            //TODO: Why does inputing the system to cartcontent (jdistlist) not cause serialiation errors, but add does.
        }
        return true;
    }

    public boolean removeOne(JRef<@Strong Product> item){
        return (cartContent.invoke("removeItem", item, true) != null);
    }

    public boolean removeMore(JRef<@Strong Product> item, int count){
        if(count < 0)
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            for(int x = 0; x < count; x++){
                if(!removeOne(item))
                    break;
            }
            return true;
        }
    }

    public boolean removeAll(JRef<@Strong Product> item){
        while(removeOne(item)){

        }
        return true;
    }

    public boolean checkout(JRef<@Strong User> user, boolean PrintReceipt, String systemInfo){
        //Sync cart to ensure it was not cleared

        cartContent.sync();
        //int len = cartContent.invoke("size", true);

        double cost = 0;
        LinkedList<JRef<@Strong Product>> cartContLocal = cartContent.invoke(
                "getAsNonReplicatedLinkedList", true);
        HashMap<JRef<@Strong Product>, Integer> countMap = new HashMap<JRef<@Strong Product>, Integer>();
        for (JRef<@Strong Product> prod: cartContLocal) {
            if(countMap.containsKey(prod))
                countMap.put(prod, countMap.get(prod) + 1);
            else
                countMap.put(prod, 1);
        }

        //Calculate Cost
        for (HashMap.Entry<JRef<@Strong Product>, Integer> element: countMap.entrySet()) {
            cost += (double) element.getKey().invoke("getCost") * element.getValue();
        }

        if(user.invoke("buy", cost, cartContLocal, systemInfo)){
            clearCart();
            if(PrintReceipt){
                System.out.println("Successfully bought:");
                for (HashMap.Entry<JRef<@Strong Product>, Integer> item: countMap.entrySet()) {
                    System.out.println(item.getValue() + " times "
                            + item.getKey().invoke("getName")
                            + " for: "
                            + (double) item.getKey().invoke("getCost") * item.getValue());
                }
                System.out.println("Total: " + cost);
            }
            return true;
        }

        return false;
    }

    public boolean clearCart(){
        if(cartContent.invoke("clear"))
            cartContent.sync();
        return true;
    }
}