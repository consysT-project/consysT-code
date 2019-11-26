package de.tuda.stg.consys.core

/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
trait ReplicaSystemJavaBinding extends ReplicaSystem  {

	/* Java interface for replicate */
	final def replicate[T <: Obj](addr : Addr, obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		replicate(addr, obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for replicate */
	final def replicate[T <: Obj](obj : T, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		replicate(obj, l)(Utils.typeTagFromCls(objCls))
	}
	/* Java interface for ref */
	final def lookup[T <: Obj](addr : Addr, objCls : Class[T], l : ConsistencyLevel) : Ref[T] = {
		lookup(addr, l)(Utils.typeTagFromCls(objCls))
	}


}
