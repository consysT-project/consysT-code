package de.tuda.stg.consys.bench;

import de.tuda.stg.consys.core.store.utils.Address;
import org.apache.curator.framework.CuratorFramework;
import org.apache.curator.framework.CuratorFrameworkFactory;
import org.apache.curator.framework.recipes.barriers.DistributedDoubleBarrier;
import org.apache.curator.retry.ExponentialBackoffRetry;

import java.time.Duration;
import java.time.temporal.ChronoUnit;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class BarrierSystem {
    private final int nReplicas;
    private final CuratorFramework curator;

    public BarrierSystem(Address address, int nReplicas) {
        this.nReplicas = nReplicas;
        curator = CuratorFrameworkFactory.newClient(address.hostname() + ":" + address.port(),
                new ExponentialBackoffRetry(250, 3));
        curator.start();
    }

    public void barrier(String name, Duration timeout) throws Exception {
        var barrier = new DistributedDoubleBarrier(curator, "/consys/bench/barrier/" + name, nReplicas);
        var success = barrier.enter(timeout.toMillis(), TimeUnit.MILLISECONDS);
        if (!success) throw new TimeoutException("timeout trying to enter barrier");
        success = barrier.leave(timeout.toMillis(), TimeUnit.MILLISECONDS);
        if (!success) throw new TimeoutException("timeout trying to leave barrier");
    }

    public void barrier(String name) throws Exception {
        barrier(name, Duration.of(5, ChronoUnit.MINUTES));
    }
}
