package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import javax.jws.soap.SOAPBinding;
import java.io.Serializable;
import java.util.LinkedList;

public class Cart implements Serializable {

    private JRef<@Weak JRefDistList> cartContent;

    Cart(JReplicaSystem system){
        cartContent = system.replicate(new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
    }

    /*
     * Add an Item to the Cart, if the item is already in the cart, add the new count to the old count,
     * if the new count is less or equal to zero return false.
     */
    public boolean add(JRef<@Strong Product> item, int count, JReplicaSystem system) throws Error{
        JRef<@Strong cartElement> itemWrapper =  cartContent.invoke("getItem", item, true);
        if(count <= 0) return false;
        if(itemWrapper == null){
            JRef<@Strong cartElement> newWrapper = system.replicate(new cartElement(item, count), JConsistencyLevel.STRONG);
            cartContent.invoke("append", newWrapper, system);
        }else {
            itemWrapper.setField("count",((int) itemWrapper.getField("count") + count));
        }
        return true;
    }

    public boolean remove(JRef<@Strong Product> item){
        return (cartContent.invoke("removeItem", item, true) != null);
    }

    public boolean increase(int count, JRef<@Strong Product> item) throws Error{
        if(count < 0)
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            JRef<@Strong cartElement> element = (JRef) cartContent.invoke("getItem", item, true);
            element.setField("count",((int) element.getField("count")  + count));
            return true;
        }
    }

    public boolean decrease(int count, JRef<@Strong Product> item){
        if(count < 0)
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            JRef<@Strong cartElement> element = (JRef) cartContent.invoke("getItem", item, true);
            int currCount = (int) element.getField("count");
            currCount = currCount - count;
            if(!(currCount > 0)){
                // if the object count is 0, simply remove the object from the cart
                return remove(item);
            }else{
                element.setField("count",currCount);
                return true;
            }
        }
    }

    public boolean checkout(JRef<@Strong User> user, JReplicaSystem system){
        //Sync cart to ensure it was not cleared
        cartContent.sync();
        int len = cartContent.invoke("size", true);

        double cost = 0;
        LinkedList<JRef<@Strong Product>> products = new LinkedList<JRef<@Strong Product>>();

        for(int i = 0; i < len; i++){
            JRef<@Strong cartElement> curr = cartContent.invoke("getIndex", i, true);
            int count = (int) curr.getField("count");
            JRef<@Strong Product> item = (JRef) curr.getField("item");
            cost += (count * (double)item.invoke("getCost"));
            while (count > 0){
                products.add(item);
                count--;
            }
        }

        if(user.invoke("buy", cost, products, system)){
            clearCart();
            System.out.println("Successfully bought:");
            for (JRef<@Strong Product> item: products) {
                System.out.println(item.invoke("getName")
                        + " for: " + item.invoke("getCost"));
            }
            System.out.println("Total: " + cost);
            return true;
        }
        return false;
    }

    public boolean clearCart(){
        if(cartContent.invoke("clear"))
            cartContent.sync();
        return true;
    }

    public class cartElement{
        public JRef<@Strong Product> item;

        public int count;

        cartElement(JRef<@Strong Product> item, int count) throws Error{
            this.item = item;
            if(count < 0)
                throw new IllegalArgumentException("Item count cannot be negative.");
            this.count = count;
        }

        //Overridden to make searching a list of cart element wrappers possible
        @Override
        public boolean equals(Object o){
            return (item.equals(o));
        }
    }
}