package de.tuda.stg.consys.objects.crdt

import akka.actor.{Actor, ActorRef}
import de.tuda.stg.consys.objects.crdt.CRDT.{Operation, ReplicaId}

import scala.collection.mutable

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
trait CRDT[T] extends Actor {

	val replicaId : ReplicaId = hashCode()

	def handleOperation(op : Operation) : Option[Any]


}



object CRDT {
	type ReplicaId = Int
	type SequenceNumber = Int


	trait Operation {
		def isReturning : Boolean = false
		def isMutating : Boolean = false
	}
	trait Mutator extends Operation {
		override def isMutating : Boolean = true
	}
	trait Accessor extends Operation {
		override def isReturning : Boolean = true
	}
}
