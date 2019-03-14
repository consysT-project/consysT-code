package de.tudarmstadt.consistency.replobj

import scala.reflect.runtime.universe._


/**
	* Created on 11.02.19.
	*
	* @author Mirko Köhler
	*/
trait ReplicaSystem[Addr] {


	/**
		* Creates a new distributed object in this store and returns a reference to that object.
		* The object can be referenced by other nodes using a path generated from the specified address.
		* @param addr The (distributed) address of the object
		* @param obj The object to distribute
		* @return A reference to the created object
		*/
	def replicate[T <: AnyRef : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[Addr, T]

	def replicate[T <: AnyRef : TypeTag](obj : T, l : ConsistencyLevel) : Ref[Addr, T]

	def ref[T <: AnyRef : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[Addr, T]


	/* Java interface for replicate */
	def replicate[T <: AnyRef, L](addr : Addr, obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[Addr, T] = {
		replicate(addr, obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for replicate */
	def replicate[T <: AnyRef, L](obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[Addr, T] = {
		replicate(obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for ref */
	def ref[T <: AnyRef, L](addr : Addr, objCls : Class[T], l : ConsistencyLevel) : Ref[Addr, T] = {
		ref(addr, l)(Utils.typeTagFromCls(objCls))
	}



}
