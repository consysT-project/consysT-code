package de.tuda.stg.consys.microbenchmarks.objectgraph;


import de.tuda.stg.consys.japi.legacy.JRef;

public class BenchmarkObject2 implements BenchmarkObject {
    public JRef<BenchmarkObject> ref0;
    public JRef<BenchmarkObject> ref1;

    public BenchmarkObject2(
            JRef<BenchmarkObject> ref0,
            JRef<BenchmarkObject> ref1) {
        this.ref0 = ref0;
        this.ref1 = ref1;
    }
}
