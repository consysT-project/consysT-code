package de.tudarmstadt.consistency.store.scala.impl

import de.tudarmstadt.consistency.store.scala.Operation

trait ReadWriteOp[-Parameter, +Arity] extends Operation[Parameter, Arity]

private case class ReadOp[T]() extends ReadWriteOp[Unit, Option[T]]
private case class WriteOp[T]() extends ReadWriteOp[T, Unit]