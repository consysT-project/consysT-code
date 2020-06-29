package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.HashMap;

public class StringHashmap extends DeltaCRDT implements Serializable {

    private HashMap<String, Serializable> map = new HashMap<String, Serializable>();

    public StringHashmap(){
        System.out.println("construktor");
    }

    public Delta addEntry(String key, Serializable value){
        System.out.println("Adding key and value:"+key.toString() + value.toString());
        map.put(key,value);

        Pair<String, Serializable> p = new Pair<String, Serializable>(key, value);
        System.out.println("transmitting Delta");
        return new Delta(p);
    }

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

    public Serializable get(String key) {
        return map.get(key);
    }

    public boolean containsKey(String key) {
        return map.containsKey(key);
    }


}
