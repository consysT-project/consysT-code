package de.tudarmstadt.consistency

import scala.language.implicitConversions
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
package object replobj {

	def typeToClassTag[T: TypeTag]: ClassTag[T] =
		ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )


	implicit def refToRob[Addr, T <: AnyRef](ref : Ref[Addr, T]) : ReplicatedObject[T] =
		ref.toReplicatedObject
}
