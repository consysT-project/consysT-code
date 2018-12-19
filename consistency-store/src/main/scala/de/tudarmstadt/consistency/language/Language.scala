package de.tudarmstadt.consistency.language

import scala.reflect.runtime.universe._


/**
	* Created on 17.12.18.
	*
	* @author Mirko Köhler
	*/
trait Language {

	type Addr
	type Consistency


	def enref[T, C <: Consistency : TypeTag](value : T) : Ref[T, C]

	def deref[T, C <: Consistency : TypeTag](ref : Ref[T, C]) : T
	def update[T, C <: Consistency : TypeTag](ref : Ref[T, C], value : T) : Unit

	def isolate[T](c : =>T) : Option[T]

	def cast[T, C <: Consistency : TypeTag](value : T) : T

	case class Ref[T, C <: Consistency : TypeTag](addr : Addr) {
		val consistencyLevel : TypeTag[C] = typeTag[C]
	}
}


