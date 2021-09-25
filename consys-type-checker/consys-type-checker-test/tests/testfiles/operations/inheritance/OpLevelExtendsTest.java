import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;

/**
 * Tests that base classes are checked for the consistency level introduced through subclass declarations.
 */
public class OpLevelExtendsTest {
    // in-order declaration
    static class Case1 {
        // :: error: consistency.type.use.incompatible
        static class Base {
            private int i;

            void setI(@Weak int j) {
                i = j;
            }
        }

        static @Mixed(StrongOp.class) class Derived extends Base {
            // since the base class methods are now @StrongOp, there is an error at setI()
        }
    }

    // out-of-order declaration
    static class Case2 {
        static @Mixed(StrongOp.class) class Derived extends Base {
            // since the base class methods are now @StrongOp, there is an error at setI()
        }

        // :: error: consistency.type.use.incompatible
        static class Base {
            private int i;

            void setI(@Weak int j) {
                i = j;
            }
        }
    }
}
