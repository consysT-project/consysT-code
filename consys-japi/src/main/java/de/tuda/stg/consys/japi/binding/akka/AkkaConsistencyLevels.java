package de.tuda.stg.consys.japi.binding.akka;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.akka.levels.Strong$;
import de.tuda.stg.consys.core.store.akka.levels.Weak$;


public class AkkaConsistencyLevels {
    public static final ConsistencyLevel<AkkaStore> STRONG = Strong$.MODULE$;
    public static final ConsistencyLevel<AkkaStore> WEAK = Weak$.MODULE$;
}
