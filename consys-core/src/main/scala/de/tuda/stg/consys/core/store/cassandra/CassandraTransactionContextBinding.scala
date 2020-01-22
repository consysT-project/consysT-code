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

	override def replicate[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RefType[T] =
		store.enref(level.toModel(store).replicateRaw[T](addr, obj, CassandraStores.getCurrentTransaction /* TODO: Is there a better way to get a transaction context? */))

	override def lookup[T <: StoreType#ObjType : TypeTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RefType[T] =
		store.enref(level.toModel(store).lookupRaw[T](addr, CassandraStores.getCurrentTransaction /* TODO: Is there a better way to get a transaction context? */))

}
