package de.tuda.stg.consys.invariants.lib.crdts;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

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

    public LWWRegister() {
        this(null);
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
