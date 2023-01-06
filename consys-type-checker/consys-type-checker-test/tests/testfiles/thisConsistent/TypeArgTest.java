package de.tuda.stg.consys.checker.testfiles.testfiles.thisConsistent;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public @Strong class TypeArgTest {
    static class A {}

    void test(Ref<@ThisConsistent A> x, Ref<@Strong A> s, Ref<@Weak A> w) {
        s = x;
        x = s;

        // :: error: (assignment)
        x = w;
    }
}
