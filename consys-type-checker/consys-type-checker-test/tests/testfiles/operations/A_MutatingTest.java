package testfiles.operations;

import de.tuda.stg.consys.annotations.ReadOnly;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;

public class A_MutatingTest {
    static class Box {
        int i = 0;
        void set(int i) { this.i = i; }
        @ReadOnly
        int get() { return i; }
    }

    static @Mixed class A {
        private Box w = new Box();

        @StrongOp
        void f() {
            w.set(0);
        }

        @WeakOp
        void g() {
            w.get();
        }

        @StrongOp
        @Strong Box getBox() {
            return w;
        }
    }
}
