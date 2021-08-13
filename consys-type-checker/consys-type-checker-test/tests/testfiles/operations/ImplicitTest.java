package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.util.List;

public class ImplicitTest {
    static class A {
        @StrongOp void f() {}
        @WeakOp void g() {}
    }

    @Transactional
    void test(Ref<@Mixed A> obj, @Weak int w, @Strong int s) {
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
    void test2(Ref<@Strong @Immutable A> s, Ref<@Weak @Immutable A> w, Ref<@Mixed List<Ref<@Mixed A>>> lm, Ref<@Mixed @Immutable A> mw, Ref<@Mixed(withDefault = StrongOp.class) @Immutable A> ms) {
        for (Ref<@Mixed A> r : lm.ref()) { // Mixed context -> treated as Weak context
            // :: error: invocation.operation.implicitflow
            r.ref().f();
            r.ref().g();

            // :: error: invocation.receiver.implicitflow
            s.ref().f();
            // :: error: invocation.receiver.implicitflow
            s.ref().g();
            w.ref().f();
            w.ref().g();

            // TODO: currently Refs are not checked for immutability on lhs
            // :: error: assignment.type.implicitflow
            mw = mw;
            // :: error: assignment.type.implicitflow :: error: immutability.assignment.type
            ms = s;
        }
    }
}
