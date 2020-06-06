package de.tuda.stg.consys.demo.counter.schema;

import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

public class AddOnlySet<T> extends DeltaCRDT {
    private Set<T> set;

    public void addElement(T el) {
        set.add(el);
        Set<T> s = new HashSet<>();
        s.add(el);
        transmitDelta(s);
    }


    @Override
    public void merge(Object other) {
        if (other instanceof Set<?>) {
            Set<T> s = (Set<T>) other;
            set.addAll(s);
        }


    }


}
