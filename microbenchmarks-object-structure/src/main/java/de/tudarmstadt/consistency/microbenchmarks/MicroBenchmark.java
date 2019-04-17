package de.tudarmstadt.consistency.microbenchmarks;

import akka.actor.Terminated;
import de.tudarmstadt.consistency.replobj.ConsistencyLevel;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject;
import de.tudarmstadt.consistency.replobj.japi.*;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;
import scala.concurrent.Await;
import scala.concurrent.Future;
import scala.concurrent.duration.Duration;

import java.util.*;
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
            replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
            replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

            replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
            replicaSystem2.addReplicaSystem("127.0.0.1", 2552);

            int count =  0;

            if (branchAtEveryLevel)
                for (int i = 0; i < depth; i++)
                    count += Math.pow(branching, i);
            else
                count = branching * (depth - 1) + 1;

            int strongCount = (int)(count * strongConsistencyRatio);

            List<ConsistencyLevel> levels = new ArrayList<>(count);
            for (int i = 0; i < count; i++)
                levels.add(JConsistencyLevel.WEAK);

            Random random = new Random(0);
            for (int i = 0, j; i < strongCount; i++) {
                do j = random.nextInt(count);
                while (levels.get(j) == JConsistencyLevel.STRONG);
                levels.set(j, JConsistencyLevel.STRONG);
            }

            Iterator<ConsistencyLevel> level = levels.iterator();

            ConsistencyLevel rootLevel = level.next();

            replicaSystem1.replicate("root", createStructure(1, level), rootLevel);

            root = replicaSystem2.ref("root", BenchmarkObject.class, rootLevel);

            Thread.sleep(1000);
        }

        public BenchmarkObject createStructure(int length, Iterator<ConsistencyLevel> level) {
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
            Future<Terminated> terminated1 = ((JReplicaSystemAkkaImpl) replicaSystem1).replicaSystem.actorSystem().terminate();
            Future<Terminated> terminated2 = ((JReplicaSystemAkkaImpl) replicaSystem2).replicaSystem.actorSystem().terminate();

            Await.ready(terminated1, Duration.apply(30, TimeUnit.SECONDS));
            Await.ready(terminated2, Duration.apply(30, TimeUnit.SECONDS));
        }
    }

    @Benchmark
    public void benchmark(BenchmarkSetup setup) {
        updateValue(0, setup.getRoot());
    }

    public void updateValue(int value, JRef<BenchmarkObject> ref) {
        BenchmarkObject object = ((AkkaReplicatedObject<?, BenchmarkObject>) ((JRefImpl<BenchmarkObject>) ref).getRef().deref()).getObject();
        if (object instanceof BenchmarkObject0)
            ref.setField("value", value);
        else if (object instanceof BenchmarkObject1)
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref0"));
        else if (object instanceof BenchmarkObject2) {
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref0"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref1"));
        }
        else if (object instanceof BenchmarkObject3) {
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref0"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref1"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref2"));
        }
        else if (object instanceof BenchmarkObject4) {
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref0"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref1"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref2"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref3"));
        }
        else if (object instanceof BenchmarkObject8) {
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref0"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref1"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref2"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref3"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref4"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref5"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref6"));
            updateValue(value, ref.<JRef<BenchmarkObject>>getField("ref7"));
        }
        else
            throw new IllegalArgumentException("Unexpected benchamrk object " + object.getClass().getName());
    }
}
