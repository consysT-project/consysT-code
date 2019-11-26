package de.tuda.stg.consys.core

import java.util.Objects

import de.tuda.stg.consys.core

import scala.language.higherKinds
import scala.reflect.runtime.universe._

/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait ReplicaSystem {

	/**
	 * Type of addresses for unique specifying replicated objects.
	 */
	type Addr

	/**
	 * Type of references to replicated objects.
	 * @tparam T The type that is referenced.
	 */
	type Ref[T <: AnyRef] <: core.Ref[Addr, T]

	def name : String

	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using a path generated from the specified address.
		* @param addr The (distributed) address of the object
		* @param obj The object to distribute
		* @return A reference to the created object
		*/
	def replicate[T <: AnyRef : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T]

	def replicate[T <: AnyRef : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T]

	def lookup[T <: AnyRef : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T]

	def close() : Unit

	final def println(any : Any) : Unit = {
		println(s"[$name] ${Objects.toString(any)}")
	}

	protected def println(msg : String) : Unit = {
		println(msg)
	}




}
