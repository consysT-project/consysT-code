package demos.counter.consystop;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import java.io.Serializable;

public class Counter implements Serializable {
    private int value;

    public Counter(@Strong int value) {
        this.value = value;
    }

    @StrongOp
    public void inc() {
        value++;
    }

    public int get() {
        return value;
    }
}
