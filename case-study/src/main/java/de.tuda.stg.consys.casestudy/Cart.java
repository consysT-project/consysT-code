package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.checkerframework.org.apache.commons.lang3.NotImplementedException;

import java.io.Serializable;

public class Cart implements Serializable {

    private JRef<@Weak JRefDistList> cartContent;

    Cart(JReplicaSystem system){
        cartContent = system.replicate(new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
    }

    //TODO: figure out how to solve the problem that we want to search by item, but items are wrapped in cartElement
    //       wrapper

    public boolean add(JRef<@Strong Product> item, int count, JReplicaSystem system) throws Error{
        JRef<@Weak cartElement> newCartElem = system.replicate(new cartElement(item, count), JConsistencyLevel.WEAK);
        return cartContent.invoke("append", newCartElem, system);
    }

    public boolean remove(JRef<@Strong Product> item){
        return (cartContent.invoke("removeItem", item) != null);
    }

    public boolean increase(int count, JRef<@Strong Product> item) throws Error{
        if(count < 0)
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            JRef<@Strong cartElement> element = (JRef) cartContent.invoke("getItem", item);
            element.setField("count",((int) element.getField("count")  + count));
            return true;
        }
    }

    public boolean decrease(int count, JRef<@Strong Product> item){
        if(count < 0)
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            JRef<@Strong cartElement> element = (JRef) cartContent.invoke("getItem", item);
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

    public class cartElement{
        public JRef<@Strong Product> item;

        public int count;

        cartElement(JRef<@Strong Product> item, int count) throws Error{
            this.item = item;
            if(count < 0)
                throw new IllegalArgumentException("Item count cannot be negative.");
            this.count = count;
        }
    }
}