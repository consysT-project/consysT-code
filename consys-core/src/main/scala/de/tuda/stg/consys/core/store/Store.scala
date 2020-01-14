package de.tuda.stg.consys.core.store

import scala.reflect.runtime.universe._
import scala.language.higherKinds

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Store extends AutoCloseable {

	type Addr
	type ObjType

	type TxContext <: TransactionContext

	type RawType[T <: ObjType] <: StoredObject[_ <: Store, T]
	type RefType[T <: ObjType] <: Handler[_ <: Store, T]

	def name : String

	def transaction[T](code : TxContext => Option[T]) : Option[T]

	def enref[T <: ObjType : TypeTag](obj : RawType[T]) : RefType[T]
}
