package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;

public class Pair<K,V > implements Serializable {

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

}