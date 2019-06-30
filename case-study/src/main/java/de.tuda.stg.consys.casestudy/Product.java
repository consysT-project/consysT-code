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

    public void printComments(){
        LinkedList<JRef<@Weak Comment>> localComments =
                comments.invoke("getAsNonReplicatedLinkedList", true);
        for (JRef<@Weak Comment> com : localComments) {
            System.out.println("----------------------------------------------");
            System.out.println(com.invoke("getAuthor") + " says: ");
            System.out.println((String) com.invoke("getContent"));
        }
    }
}
