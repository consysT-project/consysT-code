package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import de.tuda.stg.consys.checker.qual.ThisConsistent;
import de.tuda.stg.consys.checker.qual.Strong;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Strong class BoolBox implements Serializable {
    private boolean value;

    public BoolBox(@Strong boolean value) {
        this.value = value;
    }

    public void set(@Strong boolean value) {
        this.value = value;
    }

    @SideEffectFree
    public @ThisConsistent boolean get() {
        return value;
    }
}
