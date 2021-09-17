package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;

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
    void testMutable(Ref<? extends @Mutable @Mixed A> obj, @Mutable @Mixed A plain) {
        obj.ref().write();
        plain.write();
    }

    @Transactional
    void testImmutable(Ref<? extends @Immutable @Mixed A> obj, @Immutable @Mixed A plain) {
        // :: error: immutability.invocation.receiver
        obj.ref().write();
        // :: error: immutability.invocation.receiver
        plain.write();
    }

    @Transactional
    void test1(Ref<@Mutable @Mixed B> obj, @Mutable @Mixed B plain) {
        testMutable(obj, plain);
        testImmutable(obj, plain);
    }

    @Transactional
    void test2(Ref<@Immutable @Mixed(StrongOp.class) B> obj, @Immutable @Mixed(StrongOp.class) B plain) {
        // :: error: argument
        testMutable(obj, plain);
        testImmutable(obj, plain);
    }
}
