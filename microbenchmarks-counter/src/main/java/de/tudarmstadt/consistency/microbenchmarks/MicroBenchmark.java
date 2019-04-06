package de.tudarmstadt.consistency.microbenchmarks;

import akka.actor.Terminated;
import de.tudarmstadt.consistency.replobj.ConsistencyLevel;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicatedObject;
import de.tudarmstadt.consistency.replobj.java.*;
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
        @Param({"weak", "strong"})
        String level;

        JReplicaSystem replicaSystem1;
        JReplicaSystem replicaSystem2;
        JReplicaSystem replicaSystem3;

        List<JRef<Counter>> counters;

        public List<JRef<Counter>> getCounters() {
            return counters;
        }

        int index;

        public int getIndex() {
            return index;
        }

        @Setup(Level.Iteration)
        public void systemSetup() throws Exception {
            replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
            replicaSystem2 = JReplicaSystem.fromActorSystem(2553);
            replicaSystem3 = JReplicaSystem.fromActorSystem(2554);

            replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
            replicaSystem1.addReplicaSystem("127.0.0.1", 2554);
            replicaSystem2.addReplicaSystem("127.0.0.1", 2552);
            replicaSystem2.addReplicaSystem("127.0.0.1", 2554);
            replicaSystem3.addReplicaSystem("127.0.0.1", 2552);
            replicaSystem3.addReplicaSystem("127.0.0.1", 2553);

            ConsistencyLevel consistencyLevel = level.equals("weak") ? JConsistencyLevel.WEAK : JConsistencyLevel.STRONG;

            replicaSystem1.replicate("counter1", new Counter(0), consistencyLevel);
            replicaSystem2.replicate("counter2", new Counter(0), consistencyLevel);
            replicaSystem3.replicate("counter3", new Counter(0), consistencyLevel);

            counters = new ArrayList<>();
            counters.add(replicaSystem1.ref("counter1", Counter.class, consistencyLevel));
            counters.add(replicaSystem1.ref("counter2", Counter.class, consistencyLevel));
            counters.add(replicaSystem1.ref("counter3", Counter.class, consistencyLevel));
            counters.add(replicaSystem2.ref("counter1", Counter.class, consistencyLevel));
            counters.add(replicaSystem2.ref("counter2", Counter.class, consistencyLevel));
            counters.add(replicaSystem2.ref("counter3", Counter.class, consistencyLevel));
            counters.add(replicaSystem3.ref("counter1", Counter.class, consistencyLevel));
            counters.add(replicaSystem3.ref("counter2", Counter.class, consistencyLevel));
            counters.add(replicaSystem3.ref("counter3", Counter.class, consistencyLevel));

            index = -1;

            Thread.sleep(1000);
        }

        @TearDown(Level.Iteration)
        public void systemTeardown() throws Exception {
            Future<Terminated> terminated1 = ((JReplicaSystemAkkaImpl) replicaSystem1).replicaSystem.actorSystem().terminate();
            Future<Terminated> terminated2 = ((JReplicaSystemAkkaImpl) replicaSystem2).replicaSystem.actorSystem().terminate();
            Future<Terminated> terminated3 = ((JReplicaSystemAkkaImpl) replicaSystem3).replicaSystem.actorSystem().terminate();

            Await.ready(terminated1, Duration.apply(30, TimeUnit.SECONDS));
            Await.ready(terminated2, Duration.apply(30, TimeUnit.SECONDS));
            Await.ready(terminated3, Duration.apply(30, TimeUnit.SECONDS));
        }

        @Setup(Level.Invocation)
        public void indexSetup() throws Exception {
            index = (index + 1) % counters.size();
        }
    }

    @Benchmark
    public void benchmark(BenchmarkSetup setup) {
        setup.getCounters().get(setup.getIndex()).invoke("inc");
    }
}
