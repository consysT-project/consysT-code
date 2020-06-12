package de.tuda.stg.consys.demo.counter.schema;

import akka.stream.impl.fusing.Collect;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class AddOnlySet<T> extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

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
        transmitDelta(s);
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
