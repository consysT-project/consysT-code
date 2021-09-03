package de.tuda.stg.consys.demo.invariantdemos;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.core.legacy.CanBeMerged;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.japi.legacy.JRef;
import scala.Option;

public abstract class InvariantDemosBenchmark<T extends CanBeMerged<T>> extends DemoBenchmark {

    private JRef<T> ref;

    protected InvariantDemosBenchmark(String name, Config config, Option<OutputFileResolver> outputResolver, Schema<T> schema) {
        super(name, config, outputResolver);
        this.schema = schema;
    }

    private final Schema<T> schema;

    @Override
    public void setup() {
        if (processId() == 0) {
            ref = system().replicate("bench_ref", schema.newInstance(), getStrongLevel());
        } else {
            ref = system().lookup("bench_ref", schema.instanceClass(), getStrongLevel());
        }

    }

    @Override
    public void operation() {
        if (processId() != 0) {
            schema.doOperation(ref);
        }
    }



    @Override
    public void cleanup() {
        system().clear();
    }
}
