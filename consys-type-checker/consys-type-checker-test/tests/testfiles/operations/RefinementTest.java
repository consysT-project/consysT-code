package operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

/**
 * Checks that strong fields are read as weak in weak methods.
 */
public class RefinementTest {
    static @Mixed class A {
        private int i;
        private int j;

        @StrongOp
        void g() {
            i = (@Strong int) 0;
            // :: error: assignment.type.incompatible
            i = (@Weak int) 0;

            @Strong int a;
            a = i;
        }

        @WeakOp
        void f() {
            j = (@Weak int) 0;
            j = (@Strong int) 0;

            @Strong int a;
            // :: error: assignment.type.incompatible
            a = i;
            // :: error: assignment.type.incompatible
            a = this.i;
            // :: error: assignment.type.incompatible
            a = j;
        }
    }
}
