package de.tudarmstadt.consistency.microbenchmarks;

import de.tudarmstadt.consistency.replobj.java.JRef;

public class BenchmarkObject3 implements BenchmarkObject {
    public JRef<BenchmarkObject> ref0;
    public JRef<BenchmarkObject> ref1;
    public JRef<BenchmarkObject> ref2;

    public BenchmarkObject3(
            JRef<BenchmarkObject> ref0,
            JRef<BenchmarkObject> ref1,
            JRef<BenchmarkObject> ref2) {
        this.ref0 = ref0;
        this.ref1 = ref1;
        this.ref2 = ref2;
    }
}
