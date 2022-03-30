package de.tuda.stg.consys.demo.counter.schema;

import de.tuda.stg.consys.annotations.methods.*;

import java.io.Serializable;

public class Counter implements Serializable {
    private int value;

    public Counter(int value) {
        this.value = value;
    }

    @StrongOp
    public void inc() {
        value++;
    }
    @WeakOp
    public int get() {
        return value;
    }
}
