import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public class PublicTest {
    /**
     * Mixed public fields are inferred as default op level
     */
    static class A {
        public int a;
        int b;
    }

    @Transactional
    void test(Ref<@Mixed(WeakOp.class) A> objW,
              Ref<@Mixed(StrongOp.class) A> objS) {
        // :: error: assignment.type.incompatible
        @Strong int a = objW.ref().a;
        @Weak int a1 = objW.ref().a;
        // :: error: assignment.type.incompatible
        @Strong int b = objW.ref().b;
        @Weak int b1 = objW.ref().b;

        // :: error: assignment.type.incompatible
        @Local int c = objS.ref().a;
        @Strong int c1 = objS.ref().a;
        // :: error: assignment.type.incompatible
        @Local int d = objS.ref().b;
        @Strong int d1 = objS.ref().b;
    }

    /**
     * Nested classes expose private fields to outer scope, but we treat them as private regardless.
     * We instead disallow access to these fields through Ref objects.
     */
    static @Mixed(StrongOp.class) class Nested {
        private int a;
        protected int b;
        @WeakOp
        private void write() {
            a = 0;
            b = 0;
        }
    }

    @Transactional
    void testNested(Ref<Nested> obj) {
        // :: warning: ref.field.access
        obj.ref().a = 0;
        // :: warning: ref.field.access
        obj.ref().b = 0;
    }

    /**
     * Explicit annotations on public mixed class fields must match the default op level
     */
    static @Mixed(StrongOp.class) class B1 {
        // :: error: mixed.field.public.incompatible
        public @Weak int a;
        public @Strong int b;

        // :: error: mixed.field.public.incompatible
        @Weak int c;
        @Strong int d;

        protected @Weak int e;
        private @Weak int f;
    }

    /**
     * Explicit annotations on public mixed class fields must match the default op level
     */
    static @Mixed(WeakOp.class) class B2 {
        public @Weak int a;
        // :: error: mixed.field.public.incompatible
        public @Strong int b;

        @Weak int c;
        // :: error: mixed.field.public.incompatible
        @Strong int d;

        protected @Weak int e;
        private @Weak int f;
    }

    /**
     * Mixed public fields are inferred as default op level
     */
    static @Mixed(StrongOp.class) class C {
        public int a;
        int b;
        protected int c;
        private int d;

        @WeakOp
        void write() {
            // :: error: mixed.field.incompatible
            a = 0;
            // :: error: mixed.field.incompatible
            b = 0;
            c = 0;
            d = 0;
        }
    }
}
