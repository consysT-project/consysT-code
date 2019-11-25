package de.tuda.stg.consys.twitterclone.schema;

import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicaSystems;

public class Replicas {
    public static final JReplicaSystem[] replicaSystems = JReplicaSystems.fromActorSystemForTesting(4);
}
