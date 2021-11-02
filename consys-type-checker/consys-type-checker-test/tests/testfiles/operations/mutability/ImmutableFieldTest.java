import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

/**
 * Tests that explicitly given Immutable annotations on fields are respected.
 */
public @Mixed(StrongOp.class) class ImmutableFieldTest {
    private @Immutable @Strong String s;
    private @Immutable @Strong Box box;

    public ImmutableFieldTest(@Strong String v) {
        this.s = v;
        s = v;
        box = new Box();
        // :: error: immutability.assignment.type
        box.value = v;
    }

    public void set(@Strong String value) {
        // :: error: immutability.assignment.type
        this.s = value;
        // :: error: immutability.assignment.type
        s = value;
    }
}

class Box {
    public String value;
}
