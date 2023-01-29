package de.tuda.stg.consys.demo.twitterclone.schema.datacentric;

import de.tuda.stg.consys.checker.qual.Strong;

import java.io.Serializable;

public @Strong class Counter implements Serializable {
    private int value;

    public Counter() {}

    public Counter(@Strong int value) {
        this.value = value;
    }

    public void inc() {
        value++;
    }

    public int get() {
        return value;
    }
}