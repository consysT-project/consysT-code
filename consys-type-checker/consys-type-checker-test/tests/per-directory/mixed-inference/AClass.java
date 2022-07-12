package test;

import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;

public @Mixed class AClass extends ZClass {
    @WeakOp void writeDerived() {
        // :: error: mixed.inheritance.field.overwrite
        value = 0;
    }
}