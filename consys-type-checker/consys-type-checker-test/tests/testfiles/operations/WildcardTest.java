package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;

public class WildcardTest {
    static class A {

    }

    static class B extends A {

    }

    @Transactional
    void test(Ref<@Mixed ? extends @Mixed A> obj) {

    }

    @Transactional
    void test2(Ref<@Mixed(withDefault = StrongOp.class) B> obj) {
        test(obj);
    }
}
