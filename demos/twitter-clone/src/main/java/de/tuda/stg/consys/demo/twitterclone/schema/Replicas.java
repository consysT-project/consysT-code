package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.japi.JReplicaSystem;
import de.tuda.stg.consys.japi.JReplicaSystems;

public class Replicas {
    public static final JReplicaSystem[] replicaSystems = JReplicaSystems.fromActorSystemForTesting(4);
}
