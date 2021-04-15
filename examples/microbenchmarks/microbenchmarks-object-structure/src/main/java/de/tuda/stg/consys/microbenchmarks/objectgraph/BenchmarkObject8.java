package de.tuda.stg.consys.microbenchmarks.objectgraph;


import de.tuda.stg.consys.japi.legacy.JRef;

public class BenchmarkObject8 implements BenchmarkObject {
    public JRef<BenchmarkObject> ref0;
    public JRef<BenchmarkObject> ref1;
    public JRef<BenchmarkObject> ref2;
    public JRef<BenchmarkObject> ref3;
    public JRef<BenchmarkObject> ref4;
    public JRef<BenchmarkObject> ref5;
    public JRef<BenchmarkObject> ref6;
    public JRef<BenchmarkObject> ref7;

    public BenchmarkObject8(
            JRef<BenchmarkObject> ref0,
            JRef<BenchmarkObject> ref1,
            JRef<BenchmarkObject> ref2,
            JRef<BenchmarkObject> ref3,
            JRef<BenchmarkObject> ref4,
            JRef<BenchmarkObject> ref5,
            JRef<BenchmarkObject> ref6,
            JRef<BenchmarkObject> ref7) {
        this.ref0 = ref0;
        this.ref1 = ref1;
        this.ref2 = ref2;
        this.ref3 = ref3;
        this.ref4 = ref4;
        this.ref5 = ref5;
        this.ref6 = ref6;
        this.ref7 = ref7;
    }
}
