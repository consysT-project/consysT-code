package de.tuda.stg.consys.demo.rubis.schema.datacentric;

import de.tuda.stg.consys.checker.qual.*;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Strong class NumberBox<T extends @Mutable @Strong Number> implements Serializable {
    private T value;

    public NumberBox(T value) {
        this.value = value;
    }

    public void set(T value) {
        this.value = value;
    }

    @SideEffectFree
    public @Strong float floatValue() {
        return value.floatValue();
    }
}
