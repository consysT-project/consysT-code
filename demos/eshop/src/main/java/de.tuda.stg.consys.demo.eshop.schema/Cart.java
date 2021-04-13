package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.eshop.EShopLevels;
import de.tuda.stg.consys.examples.collections.JRefDistList;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

public class Cart implements Serializable{

    private JRef<@Weak JRefDistList> cartContent;

    Cart(JReplicaSystem system){
        cartContent = system.replicate(new JRefDistList(EShopLevels.getWeakLevel()), EShopLevels.getWeakLevel());
    }

    /*
     * Add an Item to the Cart, if the item is already in the cart, add the new count to the old count,
     * if the new count is less or equal to zero return false.
     */
    public boolean add(JRef<@Weak Product> item, int count) throws Error{

        if(count <= 0) return false;

        for(int x = 0;x < count;x++){
            cartContent.ref().append(item);
            //TODO: Why does inputing the system to cartcontent (jdistlist) not cause serialiation errors, but add does.
        }
        return true;
    }

    public boolean removeOne(JRef<@Weak Product> item){
        return cartContent.ref().removeItem(item, true) != null;
    }

    public boolean removeMore(JRef<@Weak Product> item, int count){
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

    public boolean removeAll(JRef<@Weak Product> item){
        while(removeOne(item)){

        }
        return true;
    }

    public boolean checkout(JRef<@Strong User> user, boolean PrintReceipt, String systemInfo){
        //Sync cart to ensure it was not cleared

        cartContent.sync();

        double cost = 0;
        LinkedList<JRef<@Weak Product>> cartContLocal = cartContent.ref().getAsNonReplicatedLinkedList(true);
        HashMap<JRef<@Weak Product>, Integer> countMap = new HashMap<JRef<@Weak Product>, Integer>();
        for (JRef<@Weak Product> prod: cartContLocal) {
            if(countMap.containsKey(prod))
                countMap.put(prod, countMap.get(prod) + 1);
            else
                countMap.put(prod, 1);
        }

        //Calculate Cost
        for (HashMap.Entry<JRef<@Weak Product>, Integer> element: countMap.entrySet()) {
            cost += (double) element.getKey().ref().getCost() * element.getValue();
        }

        if(user.ref().buy(cost, cartContLocal, systemInfo)){
            clearCart();
            if(PrintReceipt){
                System.out.println("Successfully bought:");
                for (HashMap.Entry<JRef<@Weak Product>, Integer> item: countMap.entrySet()) {
                    System.out.println(item.getValue() + " times "
                            + item.getKey().ref().getName()
                            + " for: "
                            + (double) item.getKey().ref().getCost() * item.getValue());
                }
                System.out.println("Total: " + cost);
            }
            return true;
        }

        return false;
    }

    public boolean clearCart(){
        //This is not a clean deletion, however it is not possible to solve this nicely
        if(cartContent.ref().clear())
            cartContent.sync();
        return true;
    }

    public ArrayList<JRef> getForDelete(){
        ArrayList<JRef> retList = new ArrayList<>();
        retList.addAll(cartContent.ref().getForDelete());
        //Clear function is called so that head, tail and current is correctly reset
        cartContent.ref().clear();
        return retList;
    }
}