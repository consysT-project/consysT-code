import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public @Mixed class InferenceRefTest {
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
    static void test(Ref<InferenceRefTest> obj) {
        // :: error: assignment
        Ref<@Strong A> a = obj.ref().b;
        // :: error: assignment
        Ref<@Mixed A> b = obj.ref().b;
        Ref<@Weak A> c = obj.ref().b;
    }
}
