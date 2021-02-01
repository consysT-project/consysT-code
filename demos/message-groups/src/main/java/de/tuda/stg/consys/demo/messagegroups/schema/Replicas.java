package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.japi.JReplicaSystem;
import de.tuda.stg.consys.japi.impl.JReplicaSystems;

public class Replicas {
    public static final JReplicaSystem[] replicaSystems = JReplicaSystems.fromActorSystemForTesting(4);


}
