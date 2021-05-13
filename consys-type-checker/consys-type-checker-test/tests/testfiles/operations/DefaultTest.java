package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

// TODO: If we limit default ops to extends expressions, we can skip checking the base class (all fields get same level) -> if a class has an op level specified, it must be annotated with Mixed
// TODO: also consider that we cannot check the base class if the source is not available

// TODO: add default annotations to runtime information
public class DefaultTest {
    static @Mixed(withDefault = StrongOp.class) class MixedStrong {
        int i;

        void setI(@Weak int j, @Strong int k) {
            k = i;
            // :: error: assignment.type.incompatible
            i = j;
        }
    }

    static @Mixed(withDefault = WeakOp.class) class MixedWeak {
        int i;

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment.type.incompatible
            k = i;
            i = j;
        }
    }

    static @Mixed class MixedNoDefault {
        int i;

        void setI(@Weak int j, @Strong int k) {
            // :: error: assignment.type.incompatible
            k = i;
            i = j;
        }
    }

    // ------------------------------------------------------------------------------------------------------

    static class Base {
        int i;

        // TODO: better error message, i.e. info about which derived class leads to error
        void setI(@Weak int j) {
            // :: error: assignment.type.incompatible
            i = j;
        }

        int getI() { return i; }
    }

    static @Mixed(withDefault = StrongOp.class) class Derived extends Base {
        // since the base class methods are now @StrongOp, there is an error at setI()
    }
}
