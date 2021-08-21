package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.util.List;

public class ImplicitFlowTest {
    static class A {
        @StrongOp void f() {}
        @WeakOp void g() {}
    }

    @Transactional
    void test(Ref<@Mutable @Mixed A> obj, @Weak int w, @Strong int s) {
        if (w > 0) {
            // :: error: invocation.operation.implicitflow
            obj.ref().f();
            obj.ref().g();
        }

        if (s > 0) {
            obj.ref().f();
            obj.ref().g();
        }
    }

    @Transactional
    void test2(Ref<@Mutable @Strong A> s,
               Ref<@Mutable @Weak A> w,
               Ref<@Mutable @Mixed List<Ref<@Mutable @Mixed A>>> lm,
               Ref<@Mutable @Mixed A> mw,
               Ref<@Mutable @Mixed(StrongOp.class) A> ms) {
        for (Ref<@Mutable @Mixed A> r : lm.ref()) { // Mixed context -> treated as Weak context
            // :: error: invocation.operation.implicitflow
            r.ref().f();
            r.ref().g();

            // :: error: invocation.receiver.implicitflow
            s.ref().f();
            // :: error: invocation.receiver.implicitflow
            s.ref().g();
            w.ref().f();
            w.ref().g();

            // :: error: assignment.type.implicitflow
            mw = mw;
            // :: error: assignment.type.implicitflow
            ms = ms;
        }
    }
}
