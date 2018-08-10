package de.tudarmstadt.consistency.store.scala.impl

import java.lang.annotation.Annotation

import de.tudarmstadt.consistency.store.scala.{Operation, Ref, SessionContext, Store}

/**
	* Created on 09.08.18.
	*
	* @author Mirko Köhler
	*/
trait ReadWriteStore[Key, Val] extends Store[Key, Val, ReadWriteOp] {

	type Context <: ReadWriteSessionContext

	trait ReadWriteSessionContext extends SessionContext[Key, Val, ReadWriteOp] {
		override def obtain[T <: Val](key: Key, consistencyLevel: Class[_ <: Annotation]): ReadWriteRef[Key, T]
	}
}


