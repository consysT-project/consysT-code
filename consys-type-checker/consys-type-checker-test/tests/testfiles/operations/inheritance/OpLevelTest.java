import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;

public class OpLevelTest {
    static abstract class A {
        abstract void f();
        @StrongOp abstract void g();
        @WeakOp abstract void h();
    }

    static class B {
        // :: error:
        @StrongOp void f() {}
    }

    void test(@Mutable @Mixed A a1, @Mutable @Mixed(withDefault = StrongOp.class) A a2) {
        if ((@Weak boolean) true) {
            // f is counted as WeakOp
            a1.f();
            // f is counted as StrongOp
            a2.f();
        }
    }
}
