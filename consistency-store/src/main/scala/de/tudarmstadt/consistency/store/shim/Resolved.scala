package de.tudarmstadt.consistency.store.shim

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait Resolved[+T, Ref]

object Resolved {
	case class Found[+T, Ref](resolved : Option[T], latest : T, unresolved : Set[Ref]) extends Resolved[T, Ref]
	case class NotFound[Ref]() extends Resolved[Nothing, Ref]
}


