package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Set;

public class IntegerVector extends DeltaCRDT implements Serializable {

    private Integer[] vector;

    private int length;

    public IntegerVector(int n){
        this.length = n;
        this.vector = new Integer[n];
        for (int i = 0; i < n; i++){
            vector[i] = 0;
        }
    }

    public Delta inc (int index){
        System.out.println("incrementing at index: "+index);
        vector[index] += 1;
        Pair<Integer,Integer> p = new Pair<Integer, Integer>(index,vector[index]);
        System.out.println("transmitting Delta!");
        return new Delta(p);
    }

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
}
