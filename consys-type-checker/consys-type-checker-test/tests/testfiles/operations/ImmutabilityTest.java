package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public class ImmutabilityTest {
    static class A {
        @Mutable @Strong Box box;
        void set(@Mutable @Strong Box v) {
            box = v;
        }
    }

    static class Box { int i; }

    @Transactional
    void testImmutable(Ref<@Weak @Immutable A> w) {
        // :: error: immutability.assignment.type
        w.ref().box = new Box();

        @Weak @Mutable Box b;
        // :: error: assignment.type.incompatible
        b = w.ref().box;
    }

    @Transactional
    void testMutable(Ref<@Weak @Mutable A> w) {
        w.ref().box = new Box();

        @Weak @Mutable Box b;
        b = w.ref().box;
    }

    @Transactional
    void test2(Ref<@Strong @Immutable A> immutable,
               Ref<@Strong @Mutable A> strongMutable,
               Ref<@Weak @Mutable A> weakMutable) {
        testImmutable(immutable);
        testImmutable(strongMutable);

        // :: error: argument.type.incompatible
        testMutable(immutable);
        // :: error: argument.type.incompatible
        testMutable(strongMutable);
        testMutable(weakMutable);
    }
}
