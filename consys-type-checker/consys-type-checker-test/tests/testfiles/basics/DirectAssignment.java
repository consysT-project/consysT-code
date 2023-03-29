package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class DirectAssignment {
    @Transactional
    void strongToWeak() {
        @Weak int w;
        @Strong int s = 42;
        w = s;
    }

    @Transactional
    void weakToStrong() {
        @Strong int s;
        @Weak int w = 42;
        // :: error: (assignment)
        s = w;
    }

    @Transactional
    void unannotated() {
        @Strong int a;
        @Weak int b;
        int c = 42; // unannotated variables are Inconsistent
        // :: error: (assignment)
        a = c;
        // :: error: (assignment)
        b = c;
    }
}