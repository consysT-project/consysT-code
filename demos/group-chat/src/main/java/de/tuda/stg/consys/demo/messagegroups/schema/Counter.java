package de.tuda.stg.consys.demo.messagegroups.schema;

import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public class Counter implements Serializable {
    private int value = 0;

    public void inc() {
        value = value + 1;
    }

    @SideEffectFree
    public int getValue() {
        return value;
    }
}
