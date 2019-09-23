package de.tuda.stg.consys.objects

import scala.language.higherKinds
import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait ReplicaSystem[Addr] {

	type Ref[T <: AnyRef] <: de.tuda.stg.consys.objects.Ref[Addr, T]

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

	def delete(addr : Addr) : Unit


	/* Java interface for replicate */
	final def replicate[T <: AnyRef](addr : Addr, obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		replicate(addr, obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for replicate */
	final def replicate[T <: AnyRef](obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		replicate(obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for ref */
	final def lookup[T <: AnyRef](addr : Addr, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		lookup(addr, l)(Utils.typeTagFromCls(objCls))
	}

	def close() : Unit


}
