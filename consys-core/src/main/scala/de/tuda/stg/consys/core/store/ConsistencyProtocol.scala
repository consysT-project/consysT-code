package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * A consistency model implements a protocol that is used in combinmation
 * with a store to fulfill a certain consistency level.
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
