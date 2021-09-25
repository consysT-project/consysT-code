import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

/**
 * Tests that SideEffectFree methods can be used in any implicit context.
 */
public class ImplicitFlowSideEffectTest {
    static @Mixed class A {
        @SideEffectFree
        void f() {}
    }

    @Transactional
    void test(Ref<@Mixed(WeakOp.class) A> objW, Ref<@Mixed(StrongOp.class) A> objS) {
        if ((@Weak boolean)true) {
            objW.ref().f();
            objS.ref().f();
        }
    }
}
