package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public class A_ImmutabilityTest {
    static class A { Box box; }
    static class Box {int i;}

    @Transactional
    void test(Ref<@Weak @Immutable A> w) {
        // :: error: immutability.assignment.type :: error: assignment.type.incompatible
        w.ref().box = new Box();

        // :: error: assignment.type.incompatible
        @Weak Box b = w.ref().box;
    }

    @Transactional
    void test2(Ref<@Strong @Immutable A> immutable, Ref<@Strong @Mutable A> mutable) {
        test(immutable);
        // :: error: argument.type.incompatible
        test(mutable);
    }
}
