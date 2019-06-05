package de.tuda.stg.consys.objects.crdt

import akka.actor.{Actor, ActorRef}
import de.tuda.stg.consys.objects.crdt.CRDT.{Operation, ReplicaId, SequenceNumber}
import de.tuda.stg.consys.objects.crdt.OpBasedCRDT.{Mutation, OpCache, RegisterAtReplica, RegisterReplica}

import scala.collection.mutable

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
abstract class OpBasedCRDT[T](initialState : T) extends CRDT[T] {

	protected var state : T = initialState.asInstanceOf[T]

	private val otherReplicas : mutable.Map[ReplicaId, ActorRef] = new mutable.HashMap()
	private val otherSeqs : mutable.Map[ReplicaId, SequenceNumber] = new mutable.HashMap()
	private val otherOpCache : OpCache = new OpCache()

	private var sequence : SequenceNumber = 0


	override def receive : Receive = {
		case op : Operation =>
			println(s"${self.path}: operation $op")

			if (op.isMutating) {
				sequence += 1
				val mut = Mutation(replicaId, sequence, op)
				otherReplicas.values.foreach(rep => rep ! mut)
			}

			handleOperation(op) match {
				case None =>
					require(!op.isReturning)
				case Some(ret) =>
					require(op.isReturning)
					sender() ! ret
			}

		case mut@Mutation(id, seq, op) =>
			println(s"${self.path}: mutation $mut")
			val currentSeq = otherSeqs(id)
			val nextSeq = currentSeq + 1
			//If seq is the next seqence number for replica "id"
			if (seq == nextSeq) {
				//then apply the mutation and update next seq
				handleOperation(op)
				otherSeqs(id) = nextSeq

				otherOpCache.next(id) match {
					case Some(nextMut) if nextSeq + 1 == nextMut.seq =>
						self ! nextMut
					case _ =>
				}

			} else {
				otherOpCache.cache(mut)
			}

		case RegisterReplica(id, ref) =>
			otherReplicas(id) = ref
			otherSeqs(id) = 0
			otherOpCache(id) = Nil

		case RegisterAtReplica(ref) =>
			ref ! RegisterReplica(replicaId, self)

	}
}

object OpBasedCRDT {






	case class Mutation(replicaId : ReplicaId, seq : SequenceNumber, op : Operation)

	case class RegisterReplica(replicaId : ReplicaId, actorRef : ActorRef)
	case class RegisterAtReplica(actorRef : ActorRef)



	class OpCache extends mutable.HashMap[ReplicaId, List[Mutation]] {

		def cache(mut : Mutation): Unit = get(mut.replicaId) match {
			case None => update(mut.replicaId, mut :: Nil)
			case Some(list) =>  update(mut.replicaId, insert(list, mut))
		}


		def next(id : ReplicaId) : Option[Mutation] = get(id) match {
			case None => None
			case Some(Nil) => None
			case Some(x :: xs) => Some(x)
		}



		private def insert(list : List[Mutation], mut : Mutation) : List[Mutation] = list match {
			case Nil => mut :: Nil
			case x :: xs if x.seq > mut.seq => mut :: x :: xs
			case x :: xs => x :: insert(xs, mut)
		}

	}

}
