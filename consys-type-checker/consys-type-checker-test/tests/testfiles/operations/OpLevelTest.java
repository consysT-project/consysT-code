package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

public class OpLevelTest {
    static abstract class A {
        abstract void f();
        @StrongOp abstract void g();
        @WeakOp abstract void h();
    }

    static @Mixed class B1 extends A {
        // :: error: mixed.inheritance.operation.incompatible
        @StrongOp void f() {}
        @StrongOp void g() {}
        // :: error: mixed.inheritance.operation.incompatible
        @StrongOp void h() {}
    }

    static @Mixed class B2 extends A {
        @WeakOp void f() {}
        @WeakOp void g() {}
        @WeakOp void h() {}
    }

    static @Mixed class B3 extends A {
        void f() {}
        void g() {}
        // :: error: mixed.inheritance.operation.incompatible
        void h() {}
    }

    static @Mixed class B4 extends A {
        @SideEffectFree @StrongOp void f() {}
        @SideEffectFree void g() {}
        @SideEffectFree void h() {}
    }

    static @Mixed class C extends B1 {
        // :: error: mixed.inheritance.operation.incompatible
        @StrongOp void f() {}
    }

    @Transactional void test(Ref<@Mutable @Mixed A> a1, Ref<@Mutable @Mixed(StrongOp.class) A> a2) {
        if ((@Weak boolean) true) { // weak context
            // f is counted as WeakOp -> subclasses should not override with StrongOp
            a1.ref().f();
            // f is counted as StrongOp -> counts as error
            // :: error: invocation.operation.implicitflow
            a2.ref().f();
        }
    }
}
