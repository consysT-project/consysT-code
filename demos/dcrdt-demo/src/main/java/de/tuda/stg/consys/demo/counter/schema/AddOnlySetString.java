package de.tuda.stg.consys.demo.counter.schema;

import akka.stream.impl.fusing.Collect;
import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;
import de.tuda.stg.consys.core.akka.ResultWrapper;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class AddOnlySetString extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

    private Set<String> set = new HashSet<String>();

    public AddOnlySetString() {
        System.out.println("constructor");
    }

    public Delta addElement(String str) {
        System.out.println("Adding String " + str);
        set.add(str);
        Set<String> s = new HashSet<String>();

        s.add(str);
        System.out.println("TRANSMITTING DELTA");
        return new Delta(s);
    }


    @Override
    public void merge(Object other) {
        if (other instanceof Set) {
            Set<String> s = (Set<String>) other;

            System.out.println("received delta. merging");

            set.addAll(s);
        }

        System.out.println("current state:" + toString());
    }

    @Override
    public String toString() {
        String s = "";
        for (String k : set){
            s = s + k + ",";
        }
        return s;
    }
}
