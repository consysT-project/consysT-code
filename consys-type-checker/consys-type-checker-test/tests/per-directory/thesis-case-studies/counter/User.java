package demos.counter.consystop;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.*;
import scala.Option;
import scala.concurrent.duration.Duration;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

public class User {
    private final CassandraStoreBinding store;
    private Ref<@Mutable @Mixed Counter> counter;

    public User(String host, @Local boolean init) {
        store = CassandraReplica.create(host, 9042, 2181, Duration.apply(60, "s"), init);
        store.transaction(ctx -> {
            if (init) {
                counter = ctx.replicate("counter", MIXED, Counter.class, 0);
            } else {
                counter = ctx.lookup("counter", MIXED, Counter.class);
            }
            return Option.empty();
        });
    }

    public void click() {
        store.transaction(ctx -> {
            counter.ref().inc();
            return Option.empty();
        });
    }

    public String updateDisplay() {
        return "Counter value: " + store.transaction(ctx -> Option.apply(counter.ref().get())).get();
    }

    public static void main(String[] args) {
        new User("127.0.0.1", true);
    }

    public void close() throws Exception {
        store.close();
    }
}
