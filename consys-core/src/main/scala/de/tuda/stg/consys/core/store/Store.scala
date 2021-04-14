package de.tuda.stg.consys.core.store

import scala.language.higherKinds
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * Trait for all concrete implementations of replicated data stores.
 * This class defines an interface for backend data stores that are
 * useable with the ConSysT API.
 *
 * @author Mirko Köhler
 */
trait Store extends AutoCloseable {
	/** Type for ids to identify different replicas of the store. */
	type Id

	/** Type for addresses of objects in the store. */
	type Addr
	/** Supertype for all objects that can be stored in the store. */
	type ObjType

	/** Type of transactions contexts in the store that defines what users can do with transactions. */
	type TxContext <: TransactionContext[_ <: Store]

	/** The type of handlers of stored object that handle, e.g., method calls. */
	type HandlerType[T <: ObjType] <: Handler[_ <: Store, T]
	/** The type of references to stored objects. */
	type RefType[T <: ObjType] <: Ref[_ <: Store, T]

	/** The type of levels that are useable in this store. */
	type Level <: ConsistencyLevel[_ <: Store]

	def id : Id

	def transaction[T](code : TxContext => Option[T]) : Option[T]

	override def close() : Unit = { }
}
