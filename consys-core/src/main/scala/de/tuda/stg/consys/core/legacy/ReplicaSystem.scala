package de.tuda.stg.consys.core.legacy

import java.util.Objects
import scala.language.higherKinds
import scala.reflect.runtime.universe._

/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait ReplicaSystem {

	/**
	 * Type for objects that can be stored in the store.
	 */
	type Obj

	/**
	 * Type of addresses for unique specifying replicated objects.
	 */
	type Addr

	/**
	 * Type of references to replicated objects.
	 * @tparam T The type that is referenced.
	 */
	type Ref[T <: Obj] <: de.tuda.stg.consys.core.legacy.Ref[Addr, T]


	type ConsistencyLevel


	/**
	 * The name of the replica system.
	 *
	 * @return Non-null name of the replica system.
	 */
	def name : String

	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using a path generated from the specified address.
		* @param addr The (distributed) address of the object
		* @param obj The object to distribute
		* @return A reference to the created object
		*/
	def replicate[T <: Obj : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T]

	def replicate[T <: Obj : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T]

	def lookup[T <: Obj : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T]

	def close() : Unit

	final def println(any : Any) : Unit = {
		println(s"[$name] ${Objects.toString(any)}")
	}

	protected def println(msg : String) : Unit = {
		println(msg)
	}




}
