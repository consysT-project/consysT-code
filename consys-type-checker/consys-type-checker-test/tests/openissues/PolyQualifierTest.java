package openissues;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.framework.qual.HasQualifierParameter;

public class PolyQualifierTest {
    @HasQualifierParameter(Inconsistent.class)
    static class A {
        Object o;
        void set(@PolyConsistent Object p) {
            o = p;
        }
    }

    static void use(Ref<@Strong A> obj) {

    }
}
