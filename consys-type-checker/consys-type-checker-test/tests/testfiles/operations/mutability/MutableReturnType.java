package testfiles.operations.mutability;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import org.checkerframework.dataflow.qual.SideEffectFree;

/**
 * Tests that mutable fields cannot be returned from refs.
 */
public @Weak class MutableReturnType {
    private String s;

    public String getImmutable() {
        return s;
    }

    // :: error: immutability.return.type
    @SideEffectFree
    public @Mutable @Weak String getPublic() {
        return s;
    }

    // :: error: immutability.return.type
    @SideEffectFree
    @Mutable @Weak String getPackage() {
        return s;
    }

    private @Mutable @Weak String getPrivate() {
        return s;
    }

    protected @Mutable @Weak String getProtected() {
        return s;
    }

    public static @Mutable String test(@Mutable String v) {
        return v;
    }
}
