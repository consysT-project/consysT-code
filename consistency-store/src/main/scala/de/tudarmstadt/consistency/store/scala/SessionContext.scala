package de.tudarmstadt.consistency.store.scala

import java.lang.annotation.Annotation


/**
	* Created on 08.08.18.
	*
	* @author Mirko Köhler
	*/
trait SessionContext[Key, Val, Op[_,_] <: Operation[_,_], Consistency] {

	def obtain[T <: Val](key : Key, consistencyLevel : Consistency) : Ref[T, Op]
	//the additional type parameter could specify the concrete val type that is referenced
}
