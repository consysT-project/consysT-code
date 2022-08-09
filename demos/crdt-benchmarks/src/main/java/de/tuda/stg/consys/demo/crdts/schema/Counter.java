package de.tuda.stg.consys.demo.crdts.schema;

import java.io.Serializable;

public class Counter implements Serializable {
    private int value;

    public Counter() {}

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
