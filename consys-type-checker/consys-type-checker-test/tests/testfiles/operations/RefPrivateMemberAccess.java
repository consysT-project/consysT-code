import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests that private and protected members are not accessible through Refs.
 */
public @Weak class RefPrivateMemberAccess {
    private int i;
    protected int j;
    int k;
    public int l;

    private void f1() {}
    protected void f2() {}
    void f3() {}
    public void f4() {}

    @Transactional
    static void test(Ref<@Mutable @Weak RefPrivateMemberAccess> obj) {
        // :: warning: ref.member.access
        obj.ref().i = 0;
        // :: warning: ref.member.access
        obj.ref().j = 0;
        obj.ref().k = 0;
        obj.ref().l = 0;

        // :: warning: ref.member.access
        obj.ref().f1();
        // :: warning: ref.member.access
        obj.ref().f2();
        obj.ref().f3();
        obj.ref().f4();
    }
}
