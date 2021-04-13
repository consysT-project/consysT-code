package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.eshop.EShopLevels;
import de.tuda.stg.consys.examples.collections.JRefDistList;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;
import java.util.LinkedList;

public class Product implements Serializable {

    private JRef<@Strong Double> cost;

    private double initialCost;

    private String name;

    private JRef<@Weak JRefDistList> comments;

    Product(String ProductName, double cost) {
        this.name = ProductName;
        this.initialCost = cost;
    }

    public boolean init(){
        JReplicaSystem system = JReplicaSystems.getSystem();

        cost = system.replicate(initialCost, EShopLevels.getWeakLevel());
        comments = system.replicate(new JRefDistList(EShopLevels.getWeakLevel()), EShopLevels.getWeakLevel());
        return true;
    }

    public double getCost(){
        return cost.invoke("doubleValue");
    }

    public String getName(){
        return name;
    }

    public String getComments(){
        LinkedList<JRef<@Weak Comment>> localComments =
                comments.ref().getAsNonReplicatedLinkedList( true);
        String ret = "";
        for (int x = 0; x < localComments.size(); x++){
            JRef<@Weak Comment> com = localComments.get(x);
            ret += "----------------------------------------------" + System.getProperty("line.separator");
            ret += com.invoke("getAuthor") + " says: " + System.getProperty("line.separator");
            ret += com.invoke("getContent") + System.getProperty("line.separator");
        }
        return ret;
    }
}
