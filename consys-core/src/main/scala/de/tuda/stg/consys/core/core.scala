package de.tuda.stg.consys

import scala.reflect.ClassTag

import scala.reflect.runtime.universe._


/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
package object core {

	def typeToClassTag[T: TypeTag]: ClassTag[T] =
		ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )


	implicit def refToRob[Addr, T <: AnyRef](ref : Ref[Addr, T]) : ReplicatedObject[Addr, T] =
		ref.deref
}
