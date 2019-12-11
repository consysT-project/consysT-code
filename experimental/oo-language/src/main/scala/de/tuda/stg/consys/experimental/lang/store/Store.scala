package de.tuda.stg.consys.experimental.lang.store

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Store {

	type Addr
	type ObjType

	type Context <: TxContext

	type RefType[_ <: ObjType] <: Handler[_ <: ObjType]


	def transaction[T](code : Context => Option[T]) : Option[T]

}
