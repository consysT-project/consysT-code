package de.tuda.stg.consys.demo.dcrdt.schema;

<<<<<<< HEAD
import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;

public class Pair<K,V > implements Serializable {
=======
import java.io.Serializable;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Class for Pairs
 */
public class Pair<K,V> implements Serializable {
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0

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

<<<<<<< HEAD
    private void writeObject(java.io.ObjectOutputStream out)
            throws IOException {
        out.writeObject(key);
        out.writeObject(value);
    }
    private void readObject(java.io.ObjectInputStream in)
            throws IOException, ClassNotFoundException {
        key = (K) in.readObject();
        value = (V) in.readObject();
    }
    private void readObjectNoData()
            throws ObjectStreamException {
        key = null;
        value = null;
    }

=======
    @Override
    public String toString(){
        return "(" + this.getKey().toString() + ","+ this.getValue().toString() + ")";
    }


    public void merge(Object other){
        System.out.println("should not merge!");
    }
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0
}