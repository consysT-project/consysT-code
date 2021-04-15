//package de.tuda.stg.consys.japi.binding;
//
//import de.tuda.stg.consys.core.store.ConsistencyLevel;
//import de.tuda.stg.consys.core.store.akka.*;
//import de.tuda.stg.consys.core.store.utils.Address;
//import de.tuda.stg.consys.japi.Ref;
//import de.tuda.stg.consys.japi.Replica;
//import de.tuda.stg.consys.japi.Transaction;
//import de.tuda.stg.consys.japi.TransactionContext;
//import scala.Function1;
//import scala.Option;
//import scala.collection.JavaConverters;
//import scala.concurrent.duration.FiniteDuration;
//
//import java.io.Serializable;
//
//public class Akka {
//
//    public static Option<AkkaStoreId> currentStore() {
//        return AkkaStores.getCurrentStore().map(AkkaStore::id);
//    }
//
//    public static ReplicaBinding newReplica(String host, int akkaPort, int zookeeperPort, Iterable<Address> others, FiniteDuration withTimeout) {
//        AkkaStore store = AkkaStore.fromAddress(host, akkaPort, zookeeperPort, JavaConverters.iterableAsScalaIterable(others), withTimeout);
//        return new ReplicaBinding(store);
//    }
//
//    public static class ReplicaBinding implements Replica<String, Serializable, ConsistencyLevel, TransactionContextBinding> {
//        private final AkkaStore store;
//
//        ReplicaBinding(AkkaStore store) {
//            this.store = store;
//        }
//
//        @Override
//        public <U> Option<U> transaction(Transaction<TransactionContextBinding, U, String, Serializable, ConsistencyLevel> tx) {
//            return store.transaction((Function1<AkkaTransactionContext, Option<U>>) v1 -> tx.doTransaction(new TransactionContextBinding(v1)));
//        }
//
//        @Override
//        public void close() throws Exception {
//            store.close();
//        }
//    }
//
//    public static class TransactionContextBinding implements TransactionContext<String, Serializable, ConsistencyLevel> {
//        private final AkkaTransactionContext ctx;
//
//        TransactionContextBinding(AkkaTransactionContext ctx) {
//            this.ctx = ctx;
//        }
//
//        @Override
//        public <T extends Serializable> Ref<T> replicate(String s, ConsistencyLevel level, Class<T> clazz, Object... constructorArgs) {
//            AkkaRef<T> handler = (AkkaRef<T>) ctx.replicate(s, level, clazz, constructorArgs);
//            return new RefBinding<>(handler);
//        }
//
//        @Override
//        public <T extends Serializable> Ref<T> lookup(String s, ConsistencyLevel level, Class<T> clazz) {
//            AkkaRef<T> handler = (AkkaRef<T>) ctx.lookup(s, level, clazz);
//            return new RefBinding<>(handler);
//        }
//    }
//
//    public static class RefBinding<T extends Serializable> implements Ref<T> {
//        private final AkkaRef<T> handler;
//
//        RefBinding(AkkaRef<T> handler) {
//            this.handler = handler;
//        }
//
//        @Override
//        public <R> R getField(String fieldName) {
//            return handler.resolve().getField(fieldName);
//        }
//
//        @Override
//        public <R> void setField(String fieldName, R value) {
//            handler.resolve().setField(fieldName, value);
//        }
//
//        @Override
//        public <R> R invoke(String methodName, Object... args) {
//            return handler.resolve().invoke(methodName, args);
//        }
//    }
//}
