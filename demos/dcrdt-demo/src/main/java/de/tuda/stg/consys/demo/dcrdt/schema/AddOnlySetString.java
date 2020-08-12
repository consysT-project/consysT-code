package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;
import de.tuda.stg.consys.core.akka.ResultWrapper;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Add Only Set of Strings
 */
public class AddOnlySetString extends DeltaCRDT implements Serializable {

    private Set<String> set = new HashSet<String>();

    /**
     * Constructor
     */
    public AddOnlySetString() {
        System.out.println("constructor");
    }


    /**
     * adds a String to the Set
     * @param str String that should be added
     * @return whether the set has changed. If the String was already present in this replica, returns false.
     */
    public ResultWrapper<Boolean> addElement2(String str) {
        System.out.println("Adding String " + str);
        boolean result = set.add(str);
        Set<String> s = new HashSet<String>();

        s.add(str);
        System.out.println("TRANSMITTING DELTA");
        return new ResultWrapper<>(result, s);
    }

    /**
     * adds a String to the Set
     * @param str String that should be added
     * @return Delta Object with the information which String was added
     */
    public Delta addElement(String str) {
        System.out.println("Adding String " + str);
        set.add(str);
        Set<String> s = new HashSet<String>();
        s.add(str);
        System.out.println("TRANSMITTING DELTA");
        return new Delta(s);
    }

    /**
     * merges the current Set with incoming delta messages
     * @param other delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Set) {
            Set<String> s = (Set<String>) other;

            System.out.println("received delta. merging");

            set.addAll(s);
        }
        if (other instanceof AddOnlySetString) {
            AddOnlySetString o = (AddOnlySetString) other;

            System.out.println("received delta. merging");

            set.addAll(o.set);
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
