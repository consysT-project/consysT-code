import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;

/**
 * Tests the mixed inheritance rules for fields.
 * The consistency of inherited fields cannot be changed by subclasses.
 */
public class InheritedFieldsTest {
    // base class field is weakened in separate method
    static class Case1 {
        static @Mixed class Base {
            protected int i;

            @StrongOp
            void f() {
                i = 0;
            }

            @StrongOp
            @Strong int getI() {
                return i;
            }
        }

        static @Mixed class Derived extends Base {
            @WeakOp
            void g() {
                // :: error: mixed.inheritance.field.overwrite
                i = 0; // base class field is weakened in derived class
            }
        }
    }

    // base class field is weakened in overridden method
    static class Case2 {
        static @Mixed class Base {
            protected int i;

            @StrongOp
            void f() {
                i = 0;
            }

            @StrongOp
            @Strong int getI() {
                return i;
            }
        }

        static @Mixed class Derived extends Case1.Base {
            @Override
            @WeakOp
            void f() {
                // :: error: mixed.inheritance.field.overwrite
                i = 0; // base class field is weakened in override
            }
        }
    }

    // base class field is "removed" in derived class, i.e. derived class makes field stronger
    static class Case3 {
        static @Mixed class Base {
            protected int i;

            @WeakOp
            void f() {
                i = 0;
            }
        }

        static @Mixed class Derived extends Base {
            @Override
            @WeakOp
            void f() { }

            @StrongOp
            void g() {
                // field could be strong in derived -> ignored, field stays weak
                i = (@Weak int)0;
                // :: error: assignment
                i = (@Inconsistent int)0;
            }
        }
    }
}
