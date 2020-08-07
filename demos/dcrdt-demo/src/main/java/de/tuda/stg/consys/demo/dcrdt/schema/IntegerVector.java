package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Set;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Integer vetor that only grows
 */
public class IntegerVector extends DeltaCRDT implements Serializable {

    private Integer[] vector;

    private int length;

    /**
     * Constructor; initializes all values with 0
     * @param n length of the vector
     */
    public IntegerVector(int n){
        this.length = n;
        this.vector = new Integer[n];
        for (int i = 0; i < n; i++){
            vector[i] = 0;
        }
    }

    /**
     * increases the number at the given index by 1
     * @param index index if the number that should be incremented
     * @return a delta object with the index and the new value
     */
    public Delta inc (int index){
        vector[index] += 1;
        Pair<Integer,Integer> p = new Pair<Integer, Integer>(index,vector[index]);
        return new Delta(p);
    }

    /**
     * merges the current integer vector with a delta message
     * @param other delta message
     */
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<Integer, Integer> p = (Pair<Integer, Integer>) other;

            System.out.println("received delta. merging");

            if(vector[p.getKey()]< p.getValue()){
                vector[p.getKey()] = p.getValue();
            }
        }

        System.out.println("current state:" + toString());
    }

    @Override
    public String toString(){

        String s = "";
        for(int i = 0; i<vector.length; i++){
            s+= vector[i]+ ",";
        }
        return s;
    }
}
