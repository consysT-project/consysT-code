package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.cassandra.levels.Mixed$;
import de.tuda.stg.consys.core.store.cassandra.levels.Strong$;
import de.tuda.stg.consys.core.store.cassandra.levels.Weak$;

public class CassandraConsistencyLevels {
    public static final ConsistencyLevel<CassandraStore> STRONG = Strong$.MODULE$;
    public static final ConsistencyLevel<CassandraStore> WEAK = Weak$.MODULE$;
    public static final ConsistencyLevel<CassandraStore> MIXED = Mixed$.MODULE$;
}
