package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;

/**
 * Checks that fields that are never written are @Local
 */
public @Mixed class FinalTest {
    private final int a;
    private final int b = 0;
    private int c;

    FinalTest() {
        a = 0;
    }

    @WeakOp
    int weak() { return c; }

    @StrongOp
    int strong() { return c; }

    @StrongOp
    void bla(@Strong int l) {
        // checks that a, b, c are all @Strong.
        // We cannot check that they are @Local, since they are adapted by the operation level
        l = a;
        l = b;
        l = c;
    }
}
