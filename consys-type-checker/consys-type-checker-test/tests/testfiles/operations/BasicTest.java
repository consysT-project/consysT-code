import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.next.Ref;

public class BasicTest {
    static @Replicated class A {
        int i;
        int j;

        @WeakOp
        int weak() { return i; }

        @StrongOp
        int strong() { return i + j; }

        @StrongOp
        void bla() {
            this.j = i;
        }
    }
}
