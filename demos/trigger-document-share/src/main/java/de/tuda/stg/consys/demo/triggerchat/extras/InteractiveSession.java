package de.tuda.stg.consys.demo.triggerchat.extras;


import de.tuda.stg.consys.demo.triggerchat.Session;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.concurrent.duration.Duration;

@SuppressWarnings({"consistency"})
public class InteractiveSession {
    private static final int replicasNumber = 3;
    private static final Session[] sessions = new Session[replicasNumber];

    public static void main(String[] args) {
        initConnections();
        new WebsocketServer(sessions).start();
    }

    private static void initConnections() {
        int zookeeperPort = 2181;
        for (int i = 0; i < replicasNumber; i++) {
            CassandraStoreBinding replica = CassandraReplica.create("127.0.0." + (i+1), 9042, zookeeperPort + i, Duration.apply(15, "s"), i == 0);
            sessions[i] = new Session(replica);
        }
    }
}
