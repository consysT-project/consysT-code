package de.tudarmstadt.consistency.replobj

import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait DistributedStore[Addr, Path] {

	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using a path generated from the specified address.
		* @param addr The (distributed) address of the object
		* @param value The object to distribute
		* @return A reference to the created object
		*/
	def distribute[T : TypeTag, L : TypeTag](addr : Addr, value : T) : Ref[T, L]


	def replicate[T : TypeTag, L : TypeTag](path : Path) : Ref[T, L]


	def ref[T : TypeTag, L : TypeTag](path : Path) : Ref[T, L]
}
