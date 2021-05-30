package operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class FieldAccessTest {
    static @Mixed class A implements Serializable {
        public int i;

        @Transactional
        void test(Ref<A> other) {
            // :: error: mixed.field.access
            this.i = other.ref().i;
            // :: error: mixed.field.access
            other.ref().i = this.i;

            // :: error: mixed.field.access
            i = other.ref().i;
            // :: error: mixed.field.access
            other.ref().i = i;

            i = other.ref().getI();
            this.i = other.ref().getI();

            other.ref().setI(i);
            other.ref().setI(this.i);
        }

        public @Weak int getI() {
            return i;
        }

        public void setI(@Weak int i) {
            this.i = i;
        }
    }

    @Transactional
    void test(Ref<A> o) {
        // :: error: mixed.field.access
        o.ref().i = 0; // TODO: o.ref().i <- Why is this Inconsistent ?

        // :: error: mixed.field.access
        int i = o.ref().i;
    }
}
