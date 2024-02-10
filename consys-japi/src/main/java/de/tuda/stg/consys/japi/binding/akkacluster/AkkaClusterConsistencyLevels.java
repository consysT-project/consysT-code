package de.tuda.stg.consys.japi.binding.akkacluster;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore;
import de.tuda.stg.consys.core.store.akkacluster.level.Mixed$;
import de.tuda.stg.consys.core.store.akkacluster.level.Strong$;
import de.tuda.stg.consys.core.store.akkacluster.level.Weak$;


public class AkkaClusterConsistencyLevels {
    public static final ConsistencyLevel<AkkaClusterStore> STRONG = Strong$.MODULE$;
    public static final ConsistencyLevel<AkkaClusterStore> WEAK = Weak$.MODULE$;
    public static final ConsistencyLevel<AkkaClusterStore> MIXED = Mixed$.MODULE$;
}
