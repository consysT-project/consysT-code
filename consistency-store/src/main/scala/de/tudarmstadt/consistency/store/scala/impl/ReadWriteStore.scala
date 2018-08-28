package de.tudarmstadt.consistency.store.scala.impl

import java.lang.annotation.Annotation

import de.tudarmstadt.consistency.store.scala.{Operation, Ref, SessionContext, Store}

/**
	* Created on 09.08.18.
	*
	* @author Mirko Köhler
	*/
trait ReadWriteStore[Key, Val, Consistency] extends Store[Key, Val, ReadWriteOp, Consistency] {

	type Context <: ReadWriteSessionContext

	trait ReadWriteSessionContext extends SessionContext[Key, Val, ReadWriteOp, Consistency] {
		override def obtain[T <: Val](key: Key, consistencyLevel: Consistency): ReadWriteRef[Key, T]
	}
}


