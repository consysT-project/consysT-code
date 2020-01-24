package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.TransactionContext

import scala.reflect.runtime.universe.TypeTag


/**
 * Created on 14.01.20.
 *
 * @author Mirko Köhler
 */
trait CassandraTransactionContextBinding extends TransactionContext {

	override type StoreType = CassandraStore

	override private[store] def replicateRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RawType[T] =
		level.toModel(store).replicateRaw[T](addr, obj, this.asInstanceOf[StoreType#TxContext] /* TODO: Is there a better way to get a transaction context? */)

	override private[store] def lookupRaw[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RawType[T] =
		level.toModel(store).lookupRaw[T](addr, this.asInstanceOf[StoreType#TxContext] /* TODO: Is there a better way to get a transaction context? */)

}
