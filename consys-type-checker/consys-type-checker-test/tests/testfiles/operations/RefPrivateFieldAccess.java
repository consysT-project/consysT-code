package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public @Weak class RefPrivateFieldAccess {
    private int i;
    protected int j;
    int k;
    public int l;

    @Transactional
    static void test(Ref<@Mutable @Weak RefPrivateFieldAccess> obj) {
        // :: warning: ref.field.access
        obj.ref().i = 0;
        // :: warning: ref.field.access
        obj.ref().j = 0;
        obj.ref().k = 0;
        obj.ref().l = 0;
    }
}
