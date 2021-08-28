package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public @Mixed class MiscFieldUse {
    private int i;
    private @Weak int k;

    @StrongOp void write() { i = 0; }
    @StrongOp @Strong int get() { return i; }

    @WeakOp void test() {
        if (i > 0) {

        }
    }
}
