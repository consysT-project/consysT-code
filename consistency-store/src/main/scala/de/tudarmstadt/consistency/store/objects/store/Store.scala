package de.tudarmstadt.consistency.store.objects.store

import de.tudarmstadt.consistency.store.objects.{Bindings, DistributedObjectLanguage}

import scala.util.Try

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait Store {
	self : DistributedObjectLanguage =>

	type B <: Bindings

	type OpId
	type ProcessId

	trait OperationType
	case object EnrefOp extends OperationType
	case object UpdateOp extends OperationType

	case class Operation(id : OpId, k : ProcessId, opType : OperationType, addr : B#Address, value : Any, dependencies : Set[OpId], consistency: B#Consistency)


	def freshOpId() : OpId
	def freshAddr() : B#Address

	def addOperation(op : Operation) : Try[Unit]
	def read(addr : B#Address) : Try[Set[Operation]]

}
