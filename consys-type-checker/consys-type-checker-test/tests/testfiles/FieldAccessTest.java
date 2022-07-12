package testfiles;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

/**
 * Tests type refinements when accessing fields of replicated objects.
 * The type of a field access expression should have the level of the receiver.
 * If the field is a Ref then the resulting ref type should have the weakest level between receiver and field.
 */
public class FieldAccessTest {
    static class A implements Serializable {
        int i;
        Ref<@Weak A> rw;
        Ref<@Strong A> rs;
    }

    void testObjectField(@Mutable @Strong A obj) {
        @Weak int i;
        i = obj.i;
        // :: error: assignment
        obj.i = i;
    }

    void testObjectField2(@Mutable @Weak A obj) {
        // :: error: assignment
        @Strong int i = obj.i;

        obj.i = i;
    }


    @Transactional
    void testRefField(Ref<@Mutable @Weak A> obj) {
        // :: error: assignment
        Ref<@Strong A> r = obj.ref().rs;

        obj.ref().rs = r;
    }

    @Transactional
    void testRefField2(Ref<@Mutable @Strong A> obj) {
        // :: error: assignment
        Ref<@Strong A> r = obj.ref().rw;

        obj.ref().rw = r;
    }

    @Transactional
    void testDefault(Ref<@Mutable A> obj) {
        // :: error: assignment
        Ref<@Strong A> r1 = obj.ref().rw;
        // :: error: assignment
        Ref<@Weak A> r2 = obj.ref().rw;
    }

    /**
     * Test that 'this' is ignored for field access type refinements
     */
    // :: error: consistency.type.use.incompatible
    static class ThisTest implements Serializable {
        Ref<@Mutable @Strong ThisTest> a;
        int n;

        void setRef(Ref<@Mutable @Strong ThisTest> s, Ref<@Mutable @Weak ThisTest> w) {
            a = s;
            this.a = s;
            // :: error: assignment
            a = w;
            // :: error: assignment
            this.a = w;
        }
    }
}
