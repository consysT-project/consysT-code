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

    public boolean add(JRef<@Strong Product> item, int count, JReplicaSystem system) throws Error{
        JRef<@Strong cartElement> newCartElem;
        return cartContent.invoke("append", new cartElement(item, count), system);
    }

    public boolean remove(JRef<@Strong Product> item){
        return (cartContent.invoke("removeItem", item) == null);
    }

    public boolean increase(int count, JRef<@Strong Product> item) throws Error{
        if(!(count < 0))
            throw new IllegalArgumentException("Count must be at least 0");
        else{
            JRef<@Strong cartElement> el = (JRef) cartContent.invoke("getItem", item);
        }

        throw new NotImplementedException("not implemented");
    }

    public boolean deacrease(int count){
        if(!(count < 0))
            throw new IllegalArgumentException("Count must be at least 0");


        throw new NotImplementedException("not implemented");
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