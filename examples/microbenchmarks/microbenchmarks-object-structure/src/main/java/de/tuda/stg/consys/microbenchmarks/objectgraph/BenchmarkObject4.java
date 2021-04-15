package de.tuda.stg.consys.microbenchmarks.objectgraph;


import de.tuda.stg.consys.japi.legacy.JRef;

public class BenchmarkObject4 implements BenchmarkObject {
    public JRef<BenchmarkObject> ref0;
    public JRef<BenchmarkObject> ref1;
    public JRef<BenchmarkObject> ref2;
    public JRef<BenchmarkObject> ref3;

    public BenchmarkObject4(
            JRef<BenchmarkObject> ref0,
            JRef<BenchmarkObject> ref1,
            JRef<BenchmarkObject> ref2,
            JRef<BenchmarkObject> ref3) {
        this.ref0 = ref0;
        this.ref1 = ref1;
        this.ref2 = ref2;
        this.ref3 = ref3;
    }
}
