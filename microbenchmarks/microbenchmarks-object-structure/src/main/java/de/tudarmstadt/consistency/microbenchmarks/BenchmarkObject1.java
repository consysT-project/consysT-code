package de.tudarmstadt.consistency.microbenchmarks;

import de.tudarmstadt.consistency.replobj.japi.JRef;

public class BenchmarkObject1 implements BenchmarkObject {
    public JRef<BenchmarkObject> ref0;

    public BenchmarkObject1(JRef<BenchmarkObject> ref0) {
        this.ref0 = ref0;
    }
}
