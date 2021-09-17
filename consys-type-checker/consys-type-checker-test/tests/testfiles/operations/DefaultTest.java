package test;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

import java.util.LinkedList;

public class DefaultTest {
    // ------------------------------------------------------------------------------------------------------
    // Cases for each default option

    static @Mixed(StrongOp.class) class MixedStrong {
        private int i; // inferred strong

        void setI(@Weak int j, @Strong int k) {
            k = i;
            // :: error: assignment
            i = j;
        }
    }

    static @Mixed(WeakOp.class) class MixedWeak {
        private int i; // inferred weak

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment
            k = i;
            i = j;
        }
    }

    static @Mixed class MixedNoDefault {
        private int i; // inferred weak

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment
            k = i;
            i = j;
        }
    }

    // ---------------------------------------------------------------------------------------
    // Case where inferred base class field is used in derived

    static @Mixed class Der extends LinkedList<String> {
        private @Strong int i;

        @StrongOp
        void test() {
            i = 0;
            // :: error: assignment
            i = modCount; // modCount inferred weak
        }
    }

    // ------------------------------------------------------------------------------------------------------
    // Case where base class is not compatible with derived instantiation
}
