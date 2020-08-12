package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;
/*
 * This AddOnlySet implementation is generically typed.
 * As of yet, akka does not support generics.
 */
public class AddOnlySet<T> extends DeltaCRDT implements Serializable {

    private Set<T> set = new HashSet<>();

    public AddOnlySet() {
        System.out.println("constructor");
    }
    public void addElement(T el) {
        System.out.println("Adding element " + el);
        set.add(el);
        Set<T> s = new HashSet<>();

        s.add(el);
        System.out.println("TRANSMITTING DELTA");

    }

    @Override
    public void merge(Object other) {
        if (other instanceof Set<?>) {
            Set<T> s = (Set<T>) other;

            System.out.println("received delta. merging");

            set.addAll(s);
        }

        System.out.println("current state:" + toString());
    }

    @Override
    public String toString() {
        String s = "";
        for (T k : set){
            s = s + k.toString() + ",";
        }
        return s;
    }
}
