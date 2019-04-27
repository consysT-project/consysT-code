package de.tudarmstadt.consistency.shoppingcart;

import de.tudarmstadt.consistency.replobj.japi.JReplicaSystem;

public class Replicas {

    public static final JReplicaSystem[] replicaSystems = new JReplicaSystem[4];

    static {
        for (int i = 0; i < replicaSystems.length; i++) {
            replicaSystems[i] = JReplicaSystem.fromActorSystem(2552 + i);
        }

        for (int i = 0; i < replicaSystems.length; i++) {
            for (int j = 0; j < replicaSystems.length; j++) {
                if (i != j)
                    replicaSystems[i].addReplicaSystem("127.0.0.1", 2552 + j);
            }
        }
    }
}