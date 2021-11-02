import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests that mixed inference does not change Ref<> type arguments.
 * Tests that access to Refs through Mixed class resolves to lup(field, Ref<>)
 */
public @Mixed class RefTest {
    static class A { int i; }

    private Ref<@Strong A> a; // inferred @Weak Ref<@Strong A>
    public Ref<@Strong A> b; // inferred @Weak Ref<@Strong A>

    @Transactional
    @WeakOp
    void write() {
        a.ref().i = 0;
    }

    Ref<@Strong A> get() {
        return a;
    }

    @Transactional
    static void test(Ref<RefTest> obj) {
        // :: error: assignment
        Ref<@Strong A> a = obj.ref().b;
        // :: error: assignment
        Ref<@Mixed A> b = obj.ref().b;
        Ref<@Weak A> c = obj.ref().b;
    }
}
