package de.tudarmstadt.consistency.store.scala

/**
	* Created on 09.08.18.
	*
	* @author Mirko Köhler
	*/
package object shim {

	case class Update[Id, Key, +Value](key : Key, value : Value, dependencies : Set[Id])


}
