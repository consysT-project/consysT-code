package de.tuda.stg.consys.core.store

import scala.language.higherKinds
import scala.reflect.runtime.universe._

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Store extends AutoCloseable {

	type Id

	type Addr
	type ObjType

	type TxContext <: TransactionContext

	type RawType[T <: ObjType] <: StoredObject[_ <: Store, T]
	type RefType[T <: ObjType] <: Handler[_ <: Store, T]

	def id : Id

	def transaction[T](code : TxContext => Option[T]) : Option[T]

	override def close() : Unit = { }

	protected[store] def enref[T <: ObjType : TypeTag](obj : RawType[T]) : RefType[T]
}
