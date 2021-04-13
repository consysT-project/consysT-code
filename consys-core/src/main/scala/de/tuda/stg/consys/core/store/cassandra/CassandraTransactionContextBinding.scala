package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.TransactionContext

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag


/**
 * Created on 14.01.20.
 *
 * @author Mirko Köhler
 */
trait CassandraTransactionContextBinding extends TransactionContext {

	override type StoreType = CassandraStore

	override private[store] def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, level : StoreType#Level) : StoreType#RawType[T] =
		level.toProtocol(store).writeRaw[T](addr, obj, this.asInstanceOf[StoreType#TxContext] /* TODO: Is there a better way to get a transaction context? */)

	override private[store] def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level) : StoreType#RawType[T] =
		level.toProtocol(store).readRaw[T](addr, this.asInstanceOf[StoreType#TxContext] /* TODO: Is there a better way to get a transaction context? */)

}
