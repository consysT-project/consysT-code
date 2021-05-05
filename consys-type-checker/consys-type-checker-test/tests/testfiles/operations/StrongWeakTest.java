package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

import java.io.Serializable;
// @skip-test
public class StrongWeakTest {
    static @Mixed
    class A implements Serializable {
        int w; // @Weak
        int s; // @Strong

        @WeakOp
        int weak() {
            w = 0;
            return s;
        }

        @StrongOp
        int strong() {
            return w + s;
        }

        @StrongOp
        void bla() {
            @Strong int i = s;
            s = (@Strong int)0;

            // :: error: assignment.type.incompatible
            s = w;
            // :: error: assignment.type.incompatible
            this.s = w;
            // :: error: assignment.type.incompatible
            this.s = this.w;
            // :: error: assignment.type.incompatible
            s = this.w;
        }
    }
}
