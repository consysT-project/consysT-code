package operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public class ExplicitTest {
    static @Mixed class A {
        @Strong int i;
        @Weak int j;
        int k;

        @WeakOp
        void f() {
            // :: error: mixed.field.incompatible
            i = 0;
            // :: error: mixed.field.incompatible
            this.i = 0;

            j = 0;
            this.j = 0;

            k = i;
            j = i;

            @Strong int a;
            // :: error: assignment.type.incompatible
            a = i;
        }

        @StrongOp
        void g() {
            i = 0;
            this.i = 0;

            j = 0;
            this.j = 0;

            k = i;
            j = i;

            @Strong int a;
            a = i;
        }
    }
}
