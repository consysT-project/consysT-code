package de.tuda.stg.consys.demo.dcrdt.schema;

public class Pair<K,V>{

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

}