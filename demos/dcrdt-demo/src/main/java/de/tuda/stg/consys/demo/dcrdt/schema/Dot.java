package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Class for a single Dot. Consists of an Dot-id and a Sequencenumber for ordering.
 */
public class Dot implements Serializable {

    public Pair<Integer,Integer> dot;

    /**
     * Constructor
     * @param id ID of the Dot
     * @param sequenceNumber sequence number for ordering. A higher sequence number means that the
     *                       event occurred later.
     */
    public Dot(int id, int sequenceNumber){
        this.dot = new Pair<>(id,sequenceNumber);
    }

    /**
     * Compares 2 Dots if they are equal
     * @param other The other Dot that should be compared with
     * @return true if both ID and sequence number of both Dots are equal, false otherwise
     */
    public boolean equals(Pair<Integer,Integer> other){
        return this.dot.getValue()==other.getValue() && this.dot.getKey() == other.getKey();
    }


    public String toString(){
        return "("+ this.dot.getKey()+ ";" + this.dot.getValue() +")";
    }
}
