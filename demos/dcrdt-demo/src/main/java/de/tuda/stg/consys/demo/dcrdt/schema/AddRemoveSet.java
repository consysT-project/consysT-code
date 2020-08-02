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
public class AddRemoveSet<T> extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

    //addition set
    private Set<T> addSet = new HashSet<T>();
    //tombstone set
    private Set<T> removeSet = new HashSet<T>();

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
    public Delta addElement(T el) {
        System.out.println("Adding element " + el);
        addSet.add(el);
        Set<T> s = new HashSet<T>();

        s.add(el);
        System.out.println("TRANSMITTING DELTA");
        Pair<Set<T>,Set<T>> p = new Pair<Set<T>, Set<T>>(s,null);
        return new Delta(p);
    }

    /**
     * removes an element by adding it to the "Tombstone Set"
     * @param el element that should be removed
     * @return a delta object with the new tombstone set
     */
    public Delta removeElement(T el){
        System.out.println("removing element " + el);
        removeSet.add(el);
        Set<T> s = new HashSet<T>();
        s.add(el);
        Pair<Set<T>,Set<T>> p = new Pair<Set<T>, Set<T>>(null,s);
        return new Delta(p);

    }


    /**
     * merges the current sets with the incoming delta message
     * @param other delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<Set<T>,Set<T>> p = (Pair<Set<T>,Set<T>>) other;

            System.out.println("received delta. merging");

            addSet.addAll(p.getKey());
            removeSet.addAll(p.getValue());
        }

        System.out.println("current state:" + toString());
    }

    /**
     *
     * @return the addition set
     */
    public Set<T> getAddSet() {
        return addSet;
    }

    /**
     *
     * @return the tombstone set
     */
    public Set<T> getRemoveSet() {
        return removeSet;
    }

    /**
     *
     * @return the resulting set by creating the difference from the addition set
     * with the tombstone set
     */
    public Set<T> getSet(){
        Set<T> s = new HashSet<T>();
        s.addAll(addSet);
        s.removeAll(removeSet);
        return s;
    }

    @Override
    public String toString() {
        String s = "";
        for (T k : addSet){
            s = s + k.toString() + ",";
        }
        for (T k: removeSet){
            s = s + k.toString() + ",";
        }
        return s;
    }
}
