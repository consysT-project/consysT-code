package de.tuda.stg.consys.microbenchmarks.objectgraph;

import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicatedObject;

import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;
import de.tuda.stg.consys.japi.legacy.impl.akka.JAkkaRef;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.concurrent.TimeUnit;

@Warmup(iterations = 4)
@Measurement(iterations = 4)
@BenchmarkMode(Mode.SampleTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Fork(3)
public class MicroBenchmark {
    public static void main(String[] args) throws Exception {
        Main.main(args);
    }

    @State(Scope.Benchmark)
    public static class BenchmarkSetup {
//        @Param({"0.0", "0.25", "0.5", "0.75", "1.0"})
//        double strongConsistencyRatio;
//
//        @Param({"1", "2", "4", "8"})
//        int branching;
//
//        @Param({"1", "2", "4", "8"})
//        int depth;
//
//        boolean branchAtEveryLevel = false;

        @Param({"0.0", "0.25", "0.5", "0.75", "1.0"})
        double strongConsistencyRatio;

        @Param({"1", "2", "3", "4"})
        int branching;

        @Param({"1", "2", "3", "4"})
        int depth;

        boolean branchAtEveryLevel = true;

        JReplicaSystem replicaSystem1;
        JReplicaSystem replicaSystem2;

        JRef<BenchmarkObject> root;

        public JRef<BenchmarkObject> getRoot() {
            return root;
        }

        @Setup(Level.Iteration)
        public void setup() throws Exception {
            JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);

            replicaSystem1 = systems[0];
            replicaSystem2 = systems[1];



            int count =  0;

            if (branchAtEveryLevel)
                for (int i = 0; i < depth; i++)
                    count += Math.pow(branching, i);
            else
                count = branching * (depth - 1) + 1;

            int strongCount = (int)(count * strongConsistencyRatio);

            List<ConsistencyLabel> levels = new ArrayList<>(count);
            for (int i = 0; i < count; i++)
                levels.add(JConsistencyLevels.WEAK);

            Random random = new Random(0);
            for (int i = 0, j; i < strongCount; i++) {
                do j = random.nextInt(count);
                while (levels.get(j) == JConsistencyLevels.STRONG);
                levels.set(j, JConsistencyLevels.STRONG);
            }

            Iterator<ConsistencyLabel> level = levels.iterator();

            ConsistencyLabel rootLevel = level.next();

            replicaSystem1.replicate("root", createStructure(1, level), rootLevel);

            root = replicaSystem2.lookup("root", BenchmarkObject.class, rootLevel);

            Thread.sleep(1000);
        }

        public BenchmarkObject createStructure(int length, Iterator<ConsistencyLabel> level) {
            if (length != depth) {
                if (branching == 1 || !branchAtEveryLevel && length != 1)
                    return new BenchmarkObject1(
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next())
                    );
                else if (branching == 2)
                    return new BenchmarkObject2(
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next())
                    );
                else if (branching == 3)
                    return new BenchmarkObject3(
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next())
                    );
                else if (branching == 4)
                    return new BenchmarkObject4(
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next())
                    );
                else if (branching == 8)
                    return new BenchmarkObject8(
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next()),
                            replicaSystem1.replicate(createStructure(length + 1, level), level.next())
                    );
                else
                    throw new IllegalArgumentException("Branching factor " + branching + " not supported");
            }
            else
              return new BenchmarkObject0();
        }

        @TearDown(Level.Iteration)
        public void teardown() throws Exception {
            replicaSystem1.close();
            replicaSystem2.close();
        }
    }

    @Benchmark
    public void benchmark(BenchmarkSetup setup) {
        updateValue(0, setup.getRoot());
    }

    public void updateValue(int value, JRef<BenchmarkObject> ref) {
        BenchmarkObject object = ((AkkaReplicatedObject<?, BenchmarkObject>) ((JAkkaRef<BenchmarkObject>) ref).getRef().deref()).getObject();
        if (object instanceof BenchmarkObject0)
            ref.setField("value", value);
        else if (object instanceof BenchmarkObject1)
            updateValue(value, ref.getField("ref0"));
        else if (object instanceof BenchmarkObject2) {
            updateValue(value, ref.getField("ref0"));
            updateValue(value, ref.getField("ref1"));
        }
        else if (object instanceof BenchmarkObject3) {
            updateValue(value, ref.getField("ref0"));
            updateValue(value, ref.getField("ref1"));
            updateValue(value, ref.getField("ref2"));
        }
        else if (object instanceof BenchmarkObject4) {
            updateValue(value, ref.getField("ref0"));
            updateValue(value, ref.getField("ref1"));
            updateValue(value, ref.getField("ref2"));
            updateValue(value, ref.getField("ref3"));
        }
        else if (object instanceof BenchmarkObject8) {
            updateValue(value, ref.getField("ref0"));
            updateValue(value, ref.getField("ref1"));
            updateValue(value, ref.getField("ref2"));
            updateValue(value, ref.getField("ref3"));
            updateValue(value, ref.getField("ref4"));
            updateValue(value, ref.getField("ref5"));
            updateValue(value, ref.getField("ref6"));
            updateValue(value, ref.getField("ref7"));
        }
        else
            throw new IllegalArgumentException("Unexpected benchamrk object " + object.getClass().getName());
    }
}
