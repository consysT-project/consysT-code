package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Set;

public class Hashmap<K,V> extends DeltaCRDT implements Serializable {

    private HashMap<K,V> map = new HashMap<K, V>();

    public Hashmap(){
        System.out.println("construktor");
    }

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

    @Override
    public String toString() {
        return map.toString();
    }

    public V get(K key) {
        return map.get(key);
    }

    public boolean containsKey(K key) {
        return map.containsKey(key);
    }


}
