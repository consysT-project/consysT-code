package de.tuda.stg.consys.core.store

import scala.language.higherKinds

/**
 * Trait for all concrete implementations of replicated data stores.
 *
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


	/** Returns an identifier of this replica of the store. It has to be
	 * unique for each replica. */
	def id : Id

	/**
	 * Executes a new transaction on the store. Transactions are expected
	 * to be short lived.
	 *
	 * @param body The code that is executed in the transaction.
	 * @tparam T The result type of the transaction.
	 * @return The result of the transaction or [[None]] if the transaction does
	 *         not produce a result or has been aborted by the system.
	 */
	def transaction[T](body : TxContext => Option[T]) : Option[T]

	/** Closes all connections from this store. */
	override def close() : Unit = { }
}
