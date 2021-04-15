package de.tuda.stg.consys.checker.testfiles.testfiles;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests the usage of Refs in implicit contexts.
 * Fields can be read in any context. Writing and invoking methods is only allowed when the context permits it.
 */
public class ImplicitFlowRefTest {
    static class A {
        int n;
        void f(){}
        @Weak int gw() { return 0; }
        @Strong int gs() { return 0; }
    }

    @Transactional
    void ifTest(Ref<@Strong A> s, Ref<@Weak A> w) {
        // strong context
        if (s.ref().n < s.ref().n) {
            // write to weak ref allowed
            w.ref().n = 0;

            // write to strong ref allowed
            s.ref().n = 0;
        }

        // weak context
        if (w.ref().n < w.ref().n) {
            // weak <- _: allowed
            w.ref().n = 0;
            // strong <- _: not allowed
            // :: error: (assignment.type.implicitflow)
            s.ref().n = 0;

            // weak <- weak, pure read: allowed
            @Weak int i0 = w.ref().n;
            // strong <- weak, pure read: not allowed
            // :: error: (assignment.type.implicitflow) :: error: (assignment.type.incompatible)
            @Strong int i1 = w.ref().n;

            // weak <- strong, pure read: allowed
            @Weak int j0 = s.ref().n;
            // strong <- strong, pure read: not allowed
            // :: error: (assignment.type.implicitflow)
            @Strong int j1 = s.ref().n;

            // weak <- strong, pure read, mixing refs: allowed
            w.ref().n = s.ref().n;

            // method call on weak: allowed
            w.ref().f();
            // method call on strong: not allowed
            // :: error: (invocation.receiver.implicitflow)
            s.ref().f();

            // weak <- weak, side-effect read: allowed
            @Weak int k0 = w.ref().gw();
            // weak <- strong, side-effect read: not allowed
            // :: error: (invocation.receiver.implicitflow)
            @Weak int k1 = s.ref().gs();
        }

        // mixed condition - weak context
        if (w.ref().n < s.ref().n) {
            w.ref().n = 0;
            // :: error: (assignment.type.implicitflow)
            s.ref().n = 0;
        }
    }
}
