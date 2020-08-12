package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashMap;

/**
 * @author Kris Frühwein und Julius Näumann
 */
public class DCRDTHashMap extends DeltaCRDT implements Serializable {
    private HashMap<String, DeltaCRDT> internalMap = new HashMap<>();

    /**
     * puts the given object with the key in the map
     * @param key the key of the map entry
     * @param object the object of the map entry
     * @return a delta message containing the entry
     */
    public Delta put(String key, DeltaCRDT object) {
        DeltaCRDT val = internalMap.get(key);
        if (val != null) {
            val.merge(object);
        } else {
            internalMap.put(key,object);
        }
        return new Delta(new Pair(key, object));
    }

    /**
     * merges the current map with the delta message
     * @param other delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<String, DeltaCRDT> p = (Pair<String, DeltaCRDT>) other;
            String key = p.getKey();
            DeltaCRDT val = p.getValue();

            System.out.println("received " + key + " : " + val.toString());
            DeltaCRDT oldVal = internalMap.get(key);
            if (oldVal != null) {
                System.out.println("key collision for " + key + ". Old value: " + oldVal.toString() +". Merging.");
                oldVal.merge(val);
                System.out.println("After merge: " + oldVal.toString());
            } else {
                internalMap.put(key,val);
            }
        }
    }

    /**
     * returns the object corresponding to the key
     * @param key the key of the entry
     * @return the corresponding object of the entry
     */
    public DeltaCRDT get(String key) {
        return internalMap.get(key);
    }
}
