package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Class for Pairs
 */
public class Pair<K,V> implements Serializable {

    private K key;
    private V value;

    /**
     * Constructor
     * @param k key of the pair (1st element)
     * @param v corresponding value of the pair (2nd element)
     */
    public Pair(K k, V v){
        this.key = k;
        this.value = v;
    }

    /**
     *
     * @return key of the pair (1st element)
     */
    public K getKey(){
        return this.key;
    }

    /**
     *
     * @return value of the pair (2nd element)
     */
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