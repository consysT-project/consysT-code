package de.tuda.stg.consys.demo.counter.schema;

import akka.stream.impl.fusing.Collect;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import javafx.util.Pair;

public class IntegerVector extends DeltaCRDT implements Serializable {
    // todo implement serializable!!!

    private int length;

    private Integer[] vector;

    public IntegerVector(n) {
        System.out.println("constructor");
        this.length = n;
        this.vector = new Integer[n];
        for( int i = 0; i < n; i++){
            vector[i] = 0;
        }
    }

    public Delta inc(int index){
        System.out.println("Incrementing value at index" + index);
        vector[i] += 1;

        System.out.println("Transmitting Delta");
        Pair<Integer, Integer> pair = new Pair<>(index, vector[index]);
        Delta  d = new Delta(pair);
        return d;

    }

    @Override
    public void merge(Object other) {
        if (other instanceof Pair<Integer,Integer>) {
            Pair<Integer,Integer> p = (Pair<Integer, Integer>) other;

            System.out.println("received delta. merging");
            if(vector[p.getKey()] < p.getValue() ){
                vector[p.getKey()] = p.getValue();
            }
        System.out.println("current state:" + toString());
    }

    @Override
    public String toString() {
        String s = "";
        for (int i = 0; i < vector.length; i++){
            s = s + vector[i].toString() + ",";
        }
        return s;
    }
}
