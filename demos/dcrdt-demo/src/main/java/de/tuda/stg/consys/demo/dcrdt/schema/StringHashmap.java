package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashMap;

/**
 * @author Kris Frühwein und Julius Näumann
 * This Hashmap can map from a String key to a Serializable value.
 * In the case of a key collision, behavior is undefined.
 */
public class StringHashmap extends DeltaCRDT implements Serializable {

    private HashMap<String, Serializable> map = new HashMap<String, Serializable>();

    public StringHashmap(){
        System.out.println("constructor");
    }

    /**
     * adds the value with the given key to the Hashmap
     * @param key key of the entry
     * @param value value of the entry
     * @return pair with key and entry
     */
    public Delta addEntry(String key, Serializable value){
        System.out.println("Adding key and value:"+key.toString() + value.toString());
        map.put(key,value);

        Pair<String, Serializable> p = new Pair<String, Serializable>(key, value);
        System.out.println("transmitting Delta");
        return new Delta(p);
    }

    
    /**
     * merges the current map with the delta message
     * @param other delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<String, Serializable> p = (Pair<String, Serializable>) other;

            System.out.println("received delta. merging");

            map.put(p.getKey(),p.getValue());
        }

        System.out.println("current state:" + toString());
    }

    @Override
    public String toString() {
        return map.toString();
    }

    /**
     *
     * @param key key of the entry
     * @return the value of the corresponding key
     */
    public Serializable get(String key) {
        return map.get(key);
    }

    /**
     * tells if the key is in the hashmap
     * @param key key that is checked
     * @return true if there is an entry with the given key, false otherwise
     */
    public boolean containsKey(String key) {
        return map.containsKey(key);
    }


}
