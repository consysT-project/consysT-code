package de.tuda.stg.consys.checker.testfiles.testfiles.thisConsistent;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.*;

public @Strong class MethodBodyTest {
    void test() {
        @ThisConsistent int x = 0;
        @Strong int s = 0;
        @Weak int w = 0;

        s = x;
        x = s;

        // :: error: (assignment)
        x = w;
        // :: error: (assignment)
        @Local int l = x;
    }
}