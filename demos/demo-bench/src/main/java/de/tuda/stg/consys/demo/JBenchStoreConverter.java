package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akka.AkkaReplica;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import de.tuda.stg.consys.japi.binding.akka.AkkaTransactionContextBinding;
import de.tuda.stg.consys.japi.binding.akkacluster.AkkaClusterConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akkacluster.AkkaClusterReplica;
import de.tuda.stg.consys.japi.binding.akkacluster.AkkaClusterStoreBinding;
import de.tuda.stg.consys.japi.binding.akkacluster.AkkaClusterTransactionContextBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public abstract class JBenchStoreConverter<
        Addr,
        Obj,
        TxContext extends TransactionContext<Addr, Obj, ConsistencyLevel<SStore>>,
        JStore extends Store<Addr, Obj, ConsistencyLevel<SStore>, TxContext>,
        SStore extends de.tuda.stg.consys.core.store.Store> {
    public abstract JBenchStore<Addr, Obj, TxContext, JStore, SStore> convert(SStore sstore);

    public static final JBenchStoreConverter<String, Serializable, AkkaTransactionContextBinding, AkkaStoreBinding, AkkaStore> AKKA_STORE_CONVERTER = new FromAkkaStore();

    public static final JBenchStoreConverter<String, Serializable, AkkaClusterTransactionContextBinding, AkkaClusterStoreBinding, AkkaClusterStore> AKKACLUSTER_STORE_CONVERTER = new FromAkkaClusterStore();

    public static final JBenchStoreConverter<String, Serializable, CassandraTransactionContextBinding, CassandraStoreBinding, CassandraStore> CASSANDRA_STORE_CONVERTER = new FromCassandraStore();

    private static class FromAkkaStore extends JBenchStoreConverter<String, Serializable, AkkaTransactionContextBinding, AkkaStoreBinding, AkkaStore> {
        @Override
        public JBenchStore<String, Serializable, AkkaTransactionContextBinding, AkkaStoreBinding, AkkaStore> convert(AkkaStore sstore) {
            var storeBinding = AkkaReplica.create(sstore);

            return new JBenchStore<>(sstore, storeBinding) {
                @Override
                public ConsistencyLevel<AkkaStore> getWeakLevel() {
                    return AkkaConsistencyLevels.WEAK;
                }

                @Override
                public ConsistencyLevel<AkkaStore> getStrongLevel() {
                    return AkkaConsistencyLevels.STRONG;
                }

                @Override
                public ConsistencyLevel<AkkaStore> getMixedLevel() {
                    throw new UnsupportedOperationException("akka does not support mixed levels yet.");
                }
            };
        }
    }

    private static class FromAkkaClusterStore extends JBenchStoreConverter<String, Serializable, AkkaClusterTransactionContextBinding, AkkaClusterStoreBinding, AkkaClusterStore> {
        @Override
        public JBenchStore<String, Serializable, AkkaClusterTransactionContextBinding, AkkaClusterStoreBinding, AkkaClusterStore> convert(AkkaClusterStore sstore) {
            var storeBinding = AkkaClusterReplica.create(sstore);

            return new JBenchStore<>(sstore, storeBinding) {
                @Override
                public ConsistencyLevel<AkkaClusterStore> getWeakLevel() {
                    return AkkaClusterConsistencyLevels.WEAK;
                }

                @Override
                public ConsistencyLevel<AkkaClusterStore> getStrongLevel() {
                    return AkkaClusterConsistencyLevels.STRONG;
                }

                @Override
                public ConsistencyLevel<AkkaClusterStore> getMixedLevel() {
                    return AkkaClusterConsistencyLevels.MIXED;
                }
            };
        }
    }

    private static class FromCassandraStore extends JBenchStoreConverter<String, Serializable, CassandraTransactionContextBinding, CassandraStoreBinding, CassandraStore> {
        @Override
        public JBenchStore<String, Serializable, CassandraTransactionContextBinding, CassandraStoreBinding, CassandraStore> convert(CassandraStore sstore) {
            var storeBinding = CassandraReplica.create(sstore);

            return new JBenchStore<>(sstore, storeBinding) {
                @Override
                public ConsistencyLevel<CassandraStore> getWeakLevel() {
                    return CassandraConsistencyLevels.WEAK;
                }

                @Override
                public ConsistencyLevel<CassandraStore> getStrongLevel() {
                    return CassandraConsistencyLevels.STRONG;
                }

                @Override
                public ConsistencyLevel<CassandraStore> getMixedLevel() {
                    return CassandraConsistencyLevels.MIXED;
                }
            };
        }
    }
}
