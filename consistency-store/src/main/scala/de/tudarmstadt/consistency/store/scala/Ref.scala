package de.tudarmstadt.consistency.store.scala

import scala.language.higherKinds

/**
	* A handle that corresponds to a key in the database. The handle is used to
	* perform operations on the referenced value.
	*
	* @tparam T the type of value that is referenced by this reference
	* @tparam Op the type of operations that can be performed by this reference
	*
	* @author Mirko Köhler
	*/
trait Ref[+T, Op[_,_] <: Operation[_,_]] {

	def handle[Parameter, Arity](op : Op[Parameter, Arity], parameter : Parameter) : Arity
}
