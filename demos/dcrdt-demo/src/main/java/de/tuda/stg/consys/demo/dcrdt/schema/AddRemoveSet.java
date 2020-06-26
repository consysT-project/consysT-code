package de.tuda.stg.consys.demo.dcrdt.schema;

import akka.stream.impl.fusing.Collect;
import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class AddRemoveSet<T> extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

    private Set<T> addSet = new HashSet<T>();
    private Set<T> removeSet = new HashSet<T>();

    public AddRemoveSet() {
        System.out.println("constructor");
    }

    public Delta addElement(T el) {
        System.out.println("Adding element " + el);
        addSet.add(el);
        Set<T> s = new HashSet<T>();

        s.add(el);
        System.out.println("TRANSMITTING DELTA");
        Pair<Set<T>,Set<T>> p = new Pair<Set<T>, Set<T>>(s,null);
        return new Delta(p);
    }

    public Delta removeElement(T el){
        System.out.println("removing element " + el);
        removeSet.add(el);
        Set<T> s = new HashSet<T>();
        s.add(el);
        Pair<Set<T>,Set<T>> p = new Pair<Set<T>, Set<T>>(null,s);
        return new Delta(p);

    }

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

    public Set<T> getAddSet() {
        return addSet;
    }

    public Set<T> getRemoveSet() {
        return removeSet;
    }

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
