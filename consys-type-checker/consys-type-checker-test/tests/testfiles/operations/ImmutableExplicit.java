package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

public @Mixed(StrongOp.class) class ImmutableExplicit {
    private @Immutable @Strong String s;
    private @Immutable @Strong Box box;

    public ImmutableExplicit(@Strong String v) {
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
