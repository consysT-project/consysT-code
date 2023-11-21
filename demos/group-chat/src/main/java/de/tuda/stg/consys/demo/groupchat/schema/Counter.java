package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.checker.qual.ThisConsistent;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public class Counter implements Serializable {
    private int value = 0;

    public void inc() {
        value = value + 1;
    }

    @SideEffectFree
    public @ThisConsistent int getValue() {
        return value;
    }
}
