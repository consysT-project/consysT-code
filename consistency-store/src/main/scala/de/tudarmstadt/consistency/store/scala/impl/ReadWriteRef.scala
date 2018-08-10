package de.tudarmstadt.consistency.store.scala.impl

import de.tudarmstadt.consistency.store.scala.Ref

trait ReadWriteRef[Key, T] extends Ref[T, ReadWriteOp] {

		def read() : Option[T] =
			handle(ReadOp[T](), ())

		def write(value : T) : Unit =
			handle(WriteOp[T](), value)

		def :=(value : T) : T = {
			write(value)
			value
		}

		def apply() : T =	read() match {
			case Some(value) => value
			case None => throw new IllegalArgumentException(s"no value for reference available. reference: $this" )
		}


		override def handle[Parameter, Arity](op: ReadWriteOp[Parameter, Arity], parameter: Parameter): Arity =	op match {
			case ReadOp() => handleRead().asInstanceOf[Arity]
			case WriteOp() => handleWrite(parameter.asInstanceOf[T]).asInstanceOf[Arity]
		}


		protected def handleRead() : Option[T]
		protected def handleWrite(value : T) : Unit



	}