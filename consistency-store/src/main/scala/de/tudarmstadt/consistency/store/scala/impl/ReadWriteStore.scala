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

	trait ReadWriteRef[T <: Val] extends Ref[T, ReadWriteOp] {

		def read() : Option[T] =
			handle(ReadOp, ())

		def write(value : T) : Unit =
			handle(WriteOp, value)

		def :=(value : T) : T = {
			write(value)
			value
		}

		def apply() : T =	read() match {
			case Some(value) => value
			case None => throw new IllegalArgumentException(s"no value for reference available. reference: $this" )
		}


		override def handle[Parameter, Arity](op: ReadWriteOp[Parameter, Arity], parameter: Parameter): Arity =	op match {
			case ReadOp => handleRead().asInstanceOf[Arity]
			case WriteOp => handleWrite(parameter.asInstanceOf[T]).asInstanceOf[Arity]
		}


		protected def handleRead() : Option[T]
		protected def handleWrite(value : T) : Unit


		private case object ReadOp extends ReadWriteOp[Unit, Option[T]]
		private case object WriteOp extends ReadWriteOp[T, Unit]
	}


	trait ReadWriteSessionContext extends SessionContext[Key, Val, ReadWriteOp] {
		override def obtain[T <: Val](key: Key, consistencyLevel: Class[_ <: Annotation]): ReadWriteRef[T]
	}
}

trait ReadWriteOp[-Parameter, +Arity] extends Operation[Parameter, Arity]

