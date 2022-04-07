package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

import java.io.Serializable;

public @Mixed class Counter implements Serializable {

    private int value;

    public Counter() {}

    @StrongOp
    public void inc() {
        value++;
    }

    public int get() {
        return value;
    }

    public Counter(@Strong int value) {
        this.value = value;
    }

}