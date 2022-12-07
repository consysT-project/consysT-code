import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.*;

import java.io.Serializable;

//@skip-test
public @Mixed class WriteRefTest {
    public static class A { public int v; }
    private @Weak Ref<@Strong A> w;

    @WeakOp @Transactional
    void writeWeak() {
        // :: error: mixed.field.incompatible
        w.ref().v = 0;
    }
}
