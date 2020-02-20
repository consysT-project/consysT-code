package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait StoreConsistencyModel {
	type StoreType <: Store

	def toLevel : StoreConsistencyLevel
	def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T]
	def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, txContext : StoreType#TxContext) : StoreType#RawType[T]
}
