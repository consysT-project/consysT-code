package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akka.AkkaReplica;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;

public abstract class JBenchStoreConverter<JStore extends Store, SStore extends de.tuda.stg.consys.core.store.Store> {
    public abstract JBenchStore<JStore> convert(SStore sstore);

    public static final JBenchStoreConverter<AkkaStoreBinding, AkkaStore> AKKA_STORE_CONVERTER = new FromAkkaStore();
    public static final JBenchStoreConverter<CassandraStoreBinding, CassandraStore> CASSANDRA_STORE_CONVERTER = new FromCassandraStore();

    private static class FromAkkaStore extends JBenchStoreConverter<AkkaStoreBinding, AkkaStore> {
        @Override
        public JBenchStore<AkkaStoreBinding> convert(AkkaStore sstore) {
            var storeBinding = AkkaReplica.create(sstore);

            return new JBenchStore<>(sstore, storeBinding) {
                @Override
                public ConsistencyLevel getWeakLevel() {
                    return AkkaConsistencyLevels.WEAK;
                }

                @Override
                public ConsistencyLevel getStrongLevel() {
                    return AkkaConsistencyLevels.STRONG;
                }
            };
        }
    }


    private static class FromCassandraStore extends JBenchStoreConverter<CassandraStoreBinding, CassandraStore> {
        @Override
        public JBenchStore<CassandraStoreBinding> convert(CassandraStore sstore) {
            var storeBinding = CassandraReplica.create(sstore);

            return new JBenchStore<>(sstore, storeBinding) {
                @Override
                public ConsistencyLevel getWeakLevel() {
                    return CassandraConsistencyLevels.WEAK;
                }

                @Override
                public ConsistencyLevel getStrongLevel() {
                    return CassandraConsistencyLevels.STRONG;
                }
            };
        }
    }






}





