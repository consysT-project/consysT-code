package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashMap;


/**
 * @author Kris Frühwein und Julius Näumann
 */
public class Hashmap<K extends Serializable,V extends Serializable> extends DeltaCRDT implements Serializable {

    private HashMap<K,V> map = new HashMap<K, V>();

    public Hashmap(){
        System.out.println("constructor");
    }

    /**
     * adds the key with the value as entry to the map
     * @param key key of the entry
     * @param value value of the entry
     * @return delta object with the entry as a pair
     */
    public Delta addEntry(K key, V value){
        System.out.println("Adding key and value:"+key.toString() + value.toString());
        map.put(key,value);

        Pair<K,V> p = new Pair<K, V>(key, value);
        System.out.println("transmitting Delta");
        return new Delta(p);
    }

    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<K,V> p = (Pair<K,V>) other;

            System.out.println("received delta. merging");

            map.put(p.getKey(),p.getValue());
        }

        System.out.println("current state:" + toString());
    }


    /**
     * merges the current map with the delta message
     * @param other delta message
     */
    @Override
    public String toString() {
        return map.toString();
    }

    /**
     *
     * @param key key of the entry
     * @return the value of the corresponding entry
     */
    public V get(K key) {
        return map.get(key);
    }

    /**
     * tells if the key is in the hashmap
     * @param key key that is checked
     * @return true if there is an entry with the given key, false otherwise
     */
    public boolean containsKey(K key) {
        return map.containsKey(key);
    }


}
