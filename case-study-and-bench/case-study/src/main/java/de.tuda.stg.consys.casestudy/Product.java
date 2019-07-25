package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.LinkedList;

public class Product implements Serializable {
    private double cost;

    private String name;

    public JRef<@Weak JRefDistList> comments;

    Product(String ProductName, double cost, JReplicaSystem system){
        this.name = ProductName;
        this.cost = cost;
        comments = system.replicate(new JRefDistList(JConsistencyLevel.WEAK), JConsistencyLevel.WEAK);
    }

    public double getCost(){
        return cost;
    }

    public String getName(){
        return name;
    }

    public String getComments(){
        LinkedList<JRef<@Weak Comment>> localComments =
                comments.invoke("getAsNonReplicatedLinkedList", true);
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
