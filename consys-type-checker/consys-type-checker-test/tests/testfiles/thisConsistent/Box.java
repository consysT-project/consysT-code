package de.tuda.stg.consys.checker.testfiles.testfiles.thisConsistent;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;


public @Strong class Box {
    private
    int v;

    @StrongOp
    @ThisConsistent int get() {
        return v;
    }

    @StrongOp
    void set(@ThisConsistent int v) {
        this.v = v;
    }
}

class Test {
    @Transactional
    static void testStrong(Ref<@Strong @Mutable Box> box) {
        @Strong int v1 = box.ref().get();
        box.ref().set(v1);

        @Weak int v2 = box.ref().get();
        // :: error: argument
        box.ref().set(v2);

        // :: error: assignment
        @Local int v3 = box.ref().get();
        box.ref().set(v3);
    }

    @Transactional
    static void testWeak(Ref<@Weak @Mutable Box> box) {
        @Weak int v1 = box.ref().get();
        box.ref().set(v1);

        // :: error: assignment
        @Strong int v2 = box.ref().get();
        box.ref().set(v2);

        @Inconsistent int v3 = box.ref().get();
        // :: error: argument
        box.ref().set(v3);
    }

    @Transactional
    static void testMixed(Ref<@Mixed @Mutable Box> box) {
        @Strong int v1 = box.ref().get();
        box.ref().set(v1);

        // :: error: assignment
        @Local int v2 = box.ref().get();
        box.ref().set(v2);

        @Weak int v3 = 0;
        // :: error: argument
        box.ref().set(v3);
    }
}
