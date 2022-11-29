package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import org.checkerframework.dataflow.qual.SideEffectFree;
import scala.Option;

import java.io.Serializable;
import java.util.*;

@SuppressWarnings("consistency")
@Deprecated
public class LinkedRefMap<K, V> implements Serializable {
    private Option<Ref<LinkedRefMap<K, V>>> next;
    private final Map<K, V> underlying;
    private final int batchSize;

    private static class Config {
        private static CassandraStoreBinding store;
        private static ConsistencyLevel<CassandraStore> consistencyLevel;
    }

    public LinkedRefMap() {
        this.next = null;
        this.underlying = null;
        this.batchSize = 0;
    }

    public LinkedRefMap(int batchSize) {
        if (Config.store == null || Config.consistencyLevel == null)
            throw new IllegalStateException("no store or consistency level found for RefMap");

        this.next = Option.empty();
        this.underlying = new HashMap<>(batchSize);
        this.batchSize = batchSize;
    }

    @Transactional @SideEffectFree
    public V get(K key) {
        if (underlying.containsKey(key))
            return underlying.get(key);
        if (next.isEmpty())
            return null;
        return next.get().ref().get(key);
    }

    @Transactional
    @SuppressWarnings({"unchecked"})
    public void put(K key, V value) {
        // TODO: problem is that 'put' cannot be side-effect-free an thus every node up to the insert-node is committed.
        //  We would need a run-time check for commits for this to work
        if (underlying.containsKey(key) || (next.isEmpty() && underlying.size() < batchSize)) {
            underlying.put(key, value);
        } else if (next.isEmpty()) {
            next = Config.store.transaction(ctx ->
                    Option.apply(ctx.replicate("RefMap:" + UUID.randomUUID().toString(), Config.consistencyLevel,
                            (Class<LinkedRefMap<K,V>>)(Class) LinkedRefMap.class, batchSize))
            );
        } else {
            next.get().ref().put(key, value);
        }
    }

    @Transactional
    public V remove(K key) {
        if (underlying.containsKey(key))
            return underlying.remove(key);
        if (next.isEmpty())
            return null;
        return next.get().ref().remove(key);
    }

    @Transactional @SideEffectFree
    public Collection<V> values() {
        if (next.isEmpty())
            return underlying.values();

        var nextValues = new HashSet<>(next.get().ref().values());
        nextValues.addAll(underlying.values());
        return nextValues;
    }

    @Transactional
    public boolean containsKey(K key) {
        return underlying.containsKey(key) || (next.isDefined() && next.get().ref().containsKey(key));
    }

    @SuppressWarnings("unchecked")
    public static <K, V> Ref<LinkedRefMap<K, V>> build(int batchSize, CassandraStoreBinding store,
                                                       ConsistencyLevel<CassandraStore> consistencyLevel) {
        if (Config.store == null)
            Config.store = store;
        if (Config.consistencyLevel == null)
            Config.consistencyLevel = consistencyLevel;

        return store.transaction(ctx -> Option.apply(ctx.replicate("RefMap:" + UUID.randomUUID().toString(), consistencyLevel,
                (Class<LinkedRefMap<K,V>>)(Class) LinkedRefMap.class, batchSize))
        ).get();
    }
}