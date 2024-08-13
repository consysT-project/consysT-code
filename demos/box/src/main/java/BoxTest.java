import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import org.checkerframework.dataflow.qual.SideEffectFree;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

@SuppressWarnings({"consistency"})
public class BoxTest {
    public static class Box implements Serializable {
        private int v = 0;

        @StrongOp
        public void set(int v) {
            this.v = v;
        }

        @WeakOp @SideEffectFree
        public int get() {
            return v;
        }
    }

    private static CassandraStoreBinding r0;
    private static CassandraStoreBinding r1;
    private static CassandraStoreBinding r2;
    private static final int nRuns = 5;
    private static final int msReplicaTimeout = 60000;

    public static void main(String[] args) throws Exception {
        r0 = CassandraReplica.create("127.0.0.1", 9042, new CoordinationMechanism.Zookeeper(2181), "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), true);
        r1 = CassandraReplica.create("127.0.0.2", 9042, new CoordinationMechanism.Zookeeper(2182), "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), false);
        r2 = CassandraReplica.create("127.0.0.3", 9042, new CoordinationMechanism.Zookeeper(2183), "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), false);

        int[] results = new int[nRuns];
        for (int i = 0; i < nRuns; i++) {
            results[i] = test();
        }

        long nSuccesses = Arrays.stream(results).filter(r -> r != 0).count();
        System.out.println(nSuccesses + "/" + nRuns + " runs succeeded");

        r0.close();
        r1.close();
        r2.close();
    }

    private static int test() throws Exception {
        System.out.println("run start");

        var pool = Executors.newFixedThreadPool(2);
        var tasks = new ArrayList<Callable<Object>>(2);

        // setup
        Ref<Box> box = r0.transaction(ctx -> Option.apply(ctx.replicate("box", MIXED, Box.class))).get();

        // transaction start is used as timestamp with last-write-wins (current scenario):
        // T2 starts after T1 starts and before T1 ends -> lost update of T1?
        // T1 = strong update, T2 = weak read
        // r_T1(b) |         | w_T1(b+1) |
        //         | r_T2(b) | w_T2(b)   |
        //     b=0 |     b=0 |     b=0   |

        // transaction end is used as timestamp with last-write-wins (alternative scenario):
        // T2 starts after T1 starts and before T1 ends, and T2 ends after T1 ends -> lost update of T1?
        // T1 = strong update, T2 = weak read
        // r_T1(b) |         | w_T1(b+1) |
        //         | r_T2(b) |           | w_T2(b)
        //     b=0 |     b=0 |     b=1   |     b=0

        // solutions?
        // -> no write-back on pure read transactions (weak updates still lead to lost strong updates)
        // -> separate store entries for object fields (overhead?)
        // -> different conflict resolution strategy, e.g. merging (cassandra?)

        tasks.add(() -> { // T1 (strong update)
            System.out.println("  " + new Date().toInstant() + " | start T1");
            r1.transaction(ctx -> {
                box.ref().set(1);
                try { Thread.sleep(500); } catch (InterruptedException e) { e.printStackTrace(); }
                return Option.apply(0);
            });
            System.out.println("  " + new Date().toInstant() + " | end T1");
            return null;
        });

        tasks.add(() -> { // T2 (weak read)
            try { Thread.sleep(100); } catch (InterruptedException e) { e.printStackTrace(); }
            System.out.println("  " + new Date().toInstant() + " | start T2");
            r2.transaction(ctx -> {
                box.ref().get();
                return Option.apply(0);
            });
            System.out.println("  " + new Date().toInstant() + " | end T2");
            return null;
        });

        for (var f : pool.invokeAll(tasks))
            f.get();
        pool.shutdown();

        Thread.sleep(100); // wait for all changes to propagate to r0?
        // test result
        Integer result = r0.transaction(ctx -> Option.<Integer>apply(box.ref().get())).get();
        System.out.println("  " + new Date().toInstant() + " | result: " + result);

        System.out.println("run end");
        return result;
    }
}
