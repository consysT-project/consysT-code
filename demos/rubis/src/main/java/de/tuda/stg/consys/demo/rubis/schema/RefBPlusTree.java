package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;

public class RefBPlusTree<E> {
    private final int MAX_ELEMENTS;
    private final ConsistencyLevel<CassandraStore> CONSISTENCY_LEVEL;
    private Ref<RefBPlusTree>[] children;
    private E[] elements;
    private boolean isLeaf;

    public RefBPlusTree(int degree, ConsistencyLevel<CassandraStore> consistencyLevel) {
        this.MAX_ELEMENTS = degree;
        this.CONSISTENCY_LEVEL = consistencyLevel;
    }


}
