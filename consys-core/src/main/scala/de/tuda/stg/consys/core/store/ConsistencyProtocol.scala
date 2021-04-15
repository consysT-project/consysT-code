package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag

/**
 * A consistency model implements a protocol that is used in combination
 * with a store to fulfill a certain consistency level.
 *
 * Protocols need to implement three basic functionalities:
 * <ul>
 * 	<li> Creation of references [[de.tuda.stg.consys.core.store.Ref]]. References are the
 * 	basic entities with which developers handle replicted objects. References are created
 * 	by either creating a new replicated object with ´replicate´, or looking up an existing
 * 	object with ´lookup´. </li>
 * 	<li> Usage of replicated objects. Protocols have to implement three types of operations
 * 	that are possible on replicated objects: method invocations, field reads and field writes. </li>
 * 	<li> Committing changes. Protocols implement what happens when a transactions commits. </li>
 * </ul>
 *
 */
trait ConsistencyProtocol[StoreType <: Store, Level <: ConsistencyLevel[StoreType]] {
	/** Returns the level for which this protocol holds. */
	def toLevel : Level

	def replicate[T <: StoreType#ObjType : ClassTag](txContext : StoreType#TxContext, addr : StoreType#Addr, obj : T) : StoreType#RefType[T]
	def lookup[T <: StoreType#ObjType : ClassTag](txContext : StoreType#TxContext, addr : StoreType#Addr) : StoreType#RefType[T]

	def invoke[T <: StoreType#ObjType : ClassTag, R](txContext : StoreType#TxContext, receiver : StoreType#RefType[T], methodId : String, args : Seq[Seq[Any]]) : R
	def getField[T <: StoreType#ObjType : ClassTag, R](txContext : StoreType#TxContext, receiver : StoreType#RefType[T], fieldName : String) : R
	def setField[T <: StoreType#ObjType : ClassTag, R](txContext : StoreType#TxContext, receiver : StoreType#RefType[T], fieldName : String, value : R) : Unit

	def commit(txContext : StoreType#TxContext, ref : StoreType#RefType[_ <: StoreType#ObjType]) : Unit
	def postCommit(txContext : StoreType#TxContext, ref : StoreType#RefType[_ <: StoreType#ObjType]) : Unit
}
