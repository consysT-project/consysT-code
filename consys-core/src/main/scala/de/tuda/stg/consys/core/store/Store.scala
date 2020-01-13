package de.tuda.stg.consys.core.store

import scala.language.higherKinds

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Store extends AutoCloseable {

	type Addr
	type ObjType

	type Context <: TxContext

	type RefType[_ <: ObjType] <: Handler[_ <: ObjType]

	def name : String

	def transaction[T](code : Context => Option[T]) : Option[T]

}
