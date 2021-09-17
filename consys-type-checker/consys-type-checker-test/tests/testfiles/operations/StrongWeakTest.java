package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

import java.io.Serializable;

public @Mixed class StrongWeakTest {
    private int w; // inferred @Weak
    private int s; // inferred @Strong

    @WeakOp
    int writeWeak() {
        w = 0;
        return s;
    }

    @StrongOp
    int readStrong() {
        return w + s;
    }

    @StrongOp
    void test() {
        @Strong int i = s;
        s = (@Strong int)0;

        // :: error: assignment
        s = w;
        // :: error: assignment
        this.s = w;
        // :: error: assignment
        this.s = this.w;
        // :: error: assignment
        s = this.w;
    }
}
