package test;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;

public @Mixed class ZClass {
    protected int value;

    @StrongOp void writeBase() {
        value = 0;
    }
}