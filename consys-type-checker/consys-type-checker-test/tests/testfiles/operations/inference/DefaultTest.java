import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

import java.util.LinkedList;

/**
 * Tests that the default operation level in the Mixed annotation are included during field inference.
 */
public class DefaultTest {
    // explicit StrongOp default
    static @Mixed(StrongOp.class) class MixedStrong {
        private int i; // inferred strong

        void setI(@Weak int j, @Strong int k) {
            k = i;
            // :: error: assignment
            i = j;
        }
    }

    // explicit WeakOp default
    static @Mixed(WeakOp.class) class MixedWeak {
        private int i; // inferred weak

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment
            k = i;
            i = j;
        }
    }

    // implicit WeakOp default
    static @Mixed class MixedNoDefault {
        private int i; // inferred weak

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment
            k = i;
            i = j;
        }
    }
}
