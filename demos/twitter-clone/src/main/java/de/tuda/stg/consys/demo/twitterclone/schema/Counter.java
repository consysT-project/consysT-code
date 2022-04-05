package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.methods.StrongOp;

import java.io.Serializable;

public class Counter implements Serializable {

    private int value;

    public Counter() {}

    @StrongOp
    public void inc() {
        value++;
    }

    public int get() {
        return value;
    }

    public Counter(int value) {
        this.value = value;
    }

}