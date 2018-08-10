package de.tudarmstadt.consistency.store.scala

import scala.language.higherKinds

/**
	* Created on 08.08.18.
	*
	* @author Mirko Köhler
	*/
trait Store[Key, Val, Op[_,_] <: Operation[_,_]] {

	type Context <: SessionContext[Key, Val, Op]

	type Session[R] = Context => R

	def commit[R](session: Session[R]) : R =
		session(newSessionContext())

	def newSessionContext() : Context

	def close(): Unit = {
		//Do nothing by default
	}

}
