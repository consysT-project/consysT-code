package testfiles;

import de.tuda.stg.consys.annotations.Transactional;
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

    void testObjectField(@Strong A obj) {
        @Weak int i = obj.i;
        // :: error: (assignment.type.incompatible)
        obj.i = i;
    }

    void testObjectField2(@Weak A obj) {
        // :: error: (assignment.type.incompatible)
        @Strong int i = obj.i;

        obj.i = i;
    }


    @Transactional
    void testRefField(Ref<@Weak A> obj) {
        // :: error: (assignment.type.incompatible)
        Ref<@Strong A> r = obj.ref().rs;

        obj.ref().rs = r;
    }

    @Transactional
    void testRefField2(Ref<@Strong A> obj) {
        // :: error: (assignment.type.incompatible)
        Ref<@Strong A> r = obj.ref().rw;

        obj.ref().rw = r;
    }

    @Transactional
    void testDefault(Ref<A> obj) {
        // :: error: (assignment.type.incompatible)
        Ref<@Strong A> r1 = obj.ref().rw;
        // :: error: (assignment.type.incompatible)
        Ref<@Weak A> r2 = obj.ref().rw;
    }

    /**
     * Test that 'this' is ignored for field access type refinements
     */
    static class ThisTest implements Serializable {
        Ref<@Strong ThisTest> a;
        int n;

        void setRef(Ref<@Strong ThisTest> s, Ref<@Weak ThisTest> w) {
            a = s;
            this.a = s;
            // :: error: (assignment.type.incompatible)
            a = w;
            // :: error: (assignment.type.incompatible)
            this.a = w;
        }
    }
}
