package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

public class Dot implements Serializable {

    public Pair<Integer,Integer> dot;

    public Dot(int id, int sequenceNumber){
        this.dot = new Pair<>(id,sequenceNumber);
    }


    public boolean equals(Pair<Integer,Integer> other){
        return this.dot.getValue()==other.getValue() && this.dot.getKey() == other.getKey();
    }

    public String toString(){
        return "("+ this.dot.getKey()+ ";" + this.dot.getValue() +")";
    }
}
