package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

/**
 * Tests various read access expressions.
 */
public @Mixed class ReadAccessTest {
    private int i; // inferred strong

    @StrongOp void write() { i = 0; }

    // tests that i is inferred strong
    @StrongOp @Strong int get() { return i; }

    @WeakOp void test() {
        if (i > 0) {}
        while (i < 0) {}
        switch (i) {}
        int a = i;
    }
}
