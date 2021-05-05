package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public class DefaultTest {
    // TODO: add default annotations to runtime information
    static @Mixed(withDefault = StrongOp.class) class A {
        int i;

        void setI(@Weak int j) {
            // :: error: assignment.type.incompatible
            i = j;
        }
    }

    // ------------------------------------------------------------------------------------------------------

    static class Base {
        int i;

        void setI(@Weak int j) {
            // :: error: assignment.type.incompatible
            i = j;
        }
    }

    // TODO: If we limit default ops to extends expressions, we can skip checking the base class (all fields get same level) -> if a class has an op level specified, it must be annotated with Mixed
    // TODO: also consider that we cannot check the base class if the source is not available
    static @Mixed class Derived extends @Mixed(withDefault = StrongOp.class) Base {
        void test() {

        }
    }
}
