package de.tudarmstadt.consistency.shoppingcart;

import de.tudarmstadt.consistency.replobj.japi.JReplicaSystem;

public class Replicas {

    public static final JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
    public static final JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

    public static final JReplicaSystem replicaSystem3 = JReplicaSystem.fromActorSystem(2554);
    public static final JReplicaSystem replicaSystem4 = JReplicaSystem.fromActorSystem(2555);

    static {
        replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
        replicaSystem2.addReplicaSystem("127.0.0.1", 2552);

        replicaSystem3.addReplicaSystem("127.0.0.1", 2554);
        replicaSystem4.addReplicaSystem("127.0.0.1", 2555);
    }
}