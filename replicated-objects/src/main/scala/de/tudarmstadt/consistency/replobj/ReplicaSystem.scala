package de.tudarmstadt.consistency.replobj

import scala.reflect.ClassTag
import scala.reflect.api.{TypeCreator, Universe, Mirror}
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
	def replicate[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : Ref[Addr, T, L]

	def ref[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr) : Ref[Addr, T, L]


	/* Java interface for replicate */
	def replicate[T <: AnyRef, L](addr : Addr, obj : T, objCls : Class[T], consistencyCls : Class[L]) : Ref[Addr, T, L] = {
		replicate(addr, obj)(Utils.typeTagFromCls(objCls), Utils.typeTagFromCls(consistencyCls))
	}

	/* Java interface for ref */
	def ref[T <: AnyRef, L](addr : Addr, objCls : Class[T], consistencyCls : Class[L]) : Ref[Addr, T, L] = {
		ref(addr)(Utils.typeTagFromCls(objCls), Utils.typeTagFromCls(consistencyCls))
	}



}
