package de.tuda.stg.consys.checker.testfiles.testfiles.thisConsistent;

import de.tuda.stg.consys.checker.qual.ThisConsistent;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public class MethodTest {
    @Transactional
    void test1(Ref<@Mutable @Strong Box> s, Ref<@Mutable @Weak Box> w) {
        @Strong int a;
        @Weak int b;

        a = s.ref().get();
        b = s.ref().get();

        b = w.ref().get();
        // :: error: assignment
        a = w.ref().get();
    }

    @Transactional
    void test2(Ref<@Mutable @Strong B> s, Ref<@Mutable @Weak B> w) {}
}

class Box {
    private int v;

    @ThisConsistent int get() { return v; }

    void set(@ThisConsistent int v) {
        this.v = v;
    }
}

// :: error: consistency.type.use.incompatible
class B {
    private int v;

    // error for @Strong B instance
    @ThisConsistent int f(@Weak int a) { return a; }
}