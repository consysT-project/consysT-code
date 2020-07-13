package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

public class Pair<K,V> implements Serializable {

    private K key;
    private V value;

    public Pair(K k, V v){
        this.key = k;
        this.value = v;
    }

    public K getKey(){
        return this.key;
    }

    public V getValue(){
        return this.value;
    }

    @Override
    public String toString(){
        return "(" + this.getKey().toString() + ","+ this.getValue().toString() + ")";
    }


    public void merge(Object other){
        System.out.println("should not merge!");
    }
}