package de.tuda.stg.consys.demo.dcrdt.schema;

import akka.stream.impl.fusing.Collect;
import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Set that allows adding and removing elements. Is a Tombstone set, once an element is removed,
 * it cannot be added again
 */
public class AddRemoveSet extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

    //addition set
    private Set<String> addSet = new HashSet<String>();
    //tombstone set
    private Set<String> removeSet = new HashSet<String>();

    /**
     * Constructor
     */
    public AddRemoveSet() {
        System.out.println("constructor");
    }

    /**
     * adds element to the "addidtion Set"
     * @param el element that should be added
     * @return a delta object with the new set
     */
    public Delta addElement(String el) {
        addSet.add(el);
        Set<String> s = new HashSet<String>();

        s.add(el);
        System.out.println("TRANSMITTING DELTA");
        Pair<Set<String>,Set<String>> p = new Pair<Set<String>, Set<String>>(s,null);
        return new Delta(p);
    }

    /**
     * removes an element by adding it to the "Tombstone Set"
     * @param el element that should be removed
     * @return a delta object with the new tombstone set
     */
    public Delta removeElement(String el){
        removeSet.add(el);
        Set<String> s = new HashSet<String>();
        s.add(el);
        Pair<Set<String>,Set<String>> p = new Pair<Set<String>, Set<String>>(null,s);
        return new Delta(p);

    }


    /**
     * merges the current sets with the incoming delta message
     * @param other delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<Set<String>,Set<String>> p = (Pair<Set<String>,Set<String>>) other;

            System.out.println("received delta. merging");

            if(p.getKey()!=null) {
                addSet.addAll(p.getKey());
            }
            if(p.getValue()!=null) {
                removeSet.addAll(p.getValue());
            }
        }

        System.out.println("current state:" + toString());
    }

    /**
     *
     * @return the addition set
     */
    public Set<String> getAddSet() {
        return addSet;
    }

    /**
     *
     * @return the tombstone set
     */
    public Set<String> getRemoveSet() {
        return removeSet;
    }

    /**
     *
     * @return the resulting set by creating the difference from the addition set
     * with the tombstone set
     */
    public Set<String> getSet(){
        Set<String> s = new HashSet<String>();
        s.addAll(addSet);
        s.removeAll(removeSet);
        return s;
    }

    @Override
    public String toString() {
        String s = "";
        Set<String> set = this.getSet();
        for (String k : set){
            s = s + k.toString() + ",";
        }

        return s;
    }
}
