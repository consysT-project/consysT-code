package de.tuda.stg.consys.demo.crdts.schema;

import de.tuda.stg.consys.Mergeable;

import java.io.Serializable;
@SuppressWarnings("consistency")
public class LWWRegister<T> implements Mergeable<LWWRegister<T>>, Serializable {

    private T value;
    private long timestamp;

    //@ invariant timestamp > 0;

    //@ ensures this.value == value;
    //@ ensures timestamp > 0;
    public LWWRegister(T value) {
        this.value = value;
        this.timestamp = System.currentTimeMillis();
    }

    //@ assignable value, timestamp;
    //@ ensures this.value == value;
    //@ ensures this.timestamp > \old(this.timestamp)
    public void set(T value) {
        this.value = value;
        this.timestamp = System.currentTimeMillis();
    }

    //@ ensures \result == value;
    public T get() {
        return value;
    }


    //@ requires other.timestamp != timestamp;
    //@ ensures other.timestamp > timestamp ? this.value == other.value : true;
    @Override
    public Void merge(LWWRegister<T> other) {
        if (other.timestamp > timestamp)
            value = other.value;

        return null;
    }
}
