import de.tuda.stg.consys.annotations.MethodWriteList;
import de.tuda.stg.consys.annotations.MixedField;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

public class BoxTest {
    public static class Box implements Serializable {
        public @MixedField(consistencyForWeakDefault = "strong") int v = 0;

        public Box() {
            this.v = 0;
        }

        public Box(int v) {
            this.v = v;
        }

        @StrongOp
        @MethodWriteList({"v"})
        public void set(int v) {
            this.v = v;
        }

        @WeakOp
        @MethodWriteList()
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
        r0 = Cassandra.newReplica("127.0.0.1", 9042, 2181,
                Duration.apply(msReplicaTimeout, "ms"), true);
        r1 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                Duration.apply(msReplicaTimeout, "ms"), false);
        r2 = Cassandra.newReplica("127.0.0.3", 9042, 2181,
                Duration.apply(msReplicaTimeout, "ms"), false);

        int[] results = new int[nRuns];
        for (int i = 0; i < nRuns; i++) {
            results[i] = test();
        }

        long nFails = Arrays.stream(results).filter(r -> r == 0).count();
        System.out.println(nFails + "/" + nRuns + " runs failed");

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
                return Option.empty();
            });
            System.out.println("  " + new Date().toInstant() + " | end T1");
            return null;
        });

        tasks.add(() -> { // T2 (weak read)
            try { Thread.sleep(100); } catch (InterruptedException e) { e.printStackTrace(); }
            System.out.println("  " + new Date().toInstant() + " | start T2");
            r2.transaction(ctx -> {
                box.ref().get();
                return Option.empty();
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
