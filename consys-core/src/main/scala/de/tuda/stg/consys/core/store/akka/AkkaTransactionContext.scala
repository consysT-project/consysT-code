package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.{CommitableTransactionContext, TransactionContext}

import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
case class AkkaTransactionContext(override val store : AkkaStore) extends TransactionContext
	with CommitableTransactionContext {

	override type StoreType = AkkaStore

	
	override private[store] def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support replication.")

	override private[store] def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : ConsistencyLevel) : StoreType#RawType[T] =
		throw new UnsupportedOperationException("this transaction context does not support lookups.")


	override private[store] def commit() : Unit = ???
}
