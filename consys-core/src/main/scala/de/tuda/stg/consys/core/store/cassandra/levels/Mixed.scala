//package de.tuda.stg.consys.core.store.cassandra.levels
//
//import de.tuda.stg.consys.core.store.cassandra.CassandraStore
//import scala.reflect.ClassTag
//
//
//object Mixed extends CassandraConsistencyLevel {
//
//	override def toProtocol(store : StoreType) : Protocol = new MixedProtocol(store)
//
//	private class MixedProtocol(val store : CassandraStore) extends CassandraConsistencyProtocol {
//		override def toLevel : Level = Mixed
//
//		def isStrong() : Boolean = false
//		def isWeak() : Boolean = false
//
//		override def writeRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
//			if (isStrong()) {
//				Strong.toProtocol(store).writeRaw(addr, obj, txContext)
//			} else if (isWeak()) {
//				Weak.toProtocol(store).writeRaw(addr, obj, txContext)
//			}
//
//			txContext.acquireLock(addr)
//			new StrongCassandraObject[T](addr, obj, store, txContext)
//		}
//
//		override def readRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, txContext : StoreType#TxContext) : StoreType#RawType[T] = {
//			txContext.acquireLock(addr)
//			val obj = store.CassandraBinding.readObject[T](addr, ConsistencyLevel.ALL)
//			new StrongCassandraObject[T](addr, obj, store, txContext)
//		}
//	}
//
//	private class MixedCassandraObject[T <: StoreType#ObjType : ClassTag](override val addr : String, override val state : T, txContext : StoreType#TxContext) extends CassandraObject[T] {
//		override def consistencyLevel : CassandraStore#Level = Mixed
//
//		override protected[cassandra] def writeToStore(store : CassandraStore) : Unit =
//			store.CassandraBinding.writeObject(addr, state, ConsistencyLevel.ALL, txContext.timestamp)
//	}
//
//}
