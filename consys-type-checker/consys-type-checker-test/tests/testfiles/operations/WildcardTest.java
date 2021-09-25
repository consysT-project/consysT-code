package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests inheritance with wildcards in Ref objects.
 */
public class WildcardTest {
    static class A {
        int i;
        void write() {
            i = 0;
        }
    }

    static class B extends A {
        void write() {
            i = 0;
        }
    }

    @Transactional
    void testMutable(Ref<? extends @Mutable @Mixed A> obj) {
        obj.ref().write();
    }

    @Transactional
    void testImmutable(Ref<? extends @Immutable @Mixed A> obj) {
        // :: error: immutability.invocation.receiver
        obj.ref().write();
    }

    @Transactional
    void test1(Ref<@Mutable @Mixed B> obj) {
        testMutable(obj);
        testImmutable(obj);
    }

    @Transactional
    void test2(Ref<@Immutable @Mixed(StrongOp.class) B> obj) {
        // :: error: argument
        testMutable(obj);
        testImmutable(obj);
    }
}
