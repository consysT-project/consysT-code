package de.tudarmstadt.consistency.store.objects.layer

import de.tudarmstadt.consistency.store.objects.store.Store
import de.tudarmstadt.consistency.store.objects.{Bindings, DistributedObjectLanguage}

import scala.util.{Failure, Success}

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait ConsistencyLayer extends Layer {
	self : DistributedObjectLanguage =>
	import store._

	//current state
	var lastUpdate : Option[Operation] = None
	var lastReads : Set[OpId] = Set.empty


	def enref[T](value : T, consistency : B#Consistency) : StoreRef[T] = {
		val opId = freshOpId()
		val addr = freshAddr()
		val op = Operation(opId, k, EnrefOp, addr, value, lastReads ++ lastUpdate.map(_.id), consistency)

		addOperation(op) match {
			case Success(_) =>
				lastUpdate = Some(op)
				lastReads = Set.empty
				StoreRef(addr, consistency)

			case Failure(exception) =>
				//TODO: Do error handling
				throw exception
		}
	}

	def deref[T](ref : StoreRef[T]) : T = read(ref.addr) match {
		case Success(ops) => ???

//
//			lastReads += op.id
//			op.value.asInstanceOf[T]

		case Failure(exception) =>
			//TODO: Do error handling
			throw exception
	}



	def update[T](ref : StoreRef[T], value : T) : Unit = {
		val opId = freshOpId()
		val op = Operation(opId, k, EnrefOp, ref.addr, value, lastReads ++ lastUpdate.map(_.id), ref.consistency)

		addOperation(op) match {
			case Success(_) =>
				lastUpdate = Some(op)
				lastReads = Set.empty

			case Failure(exception) =>
				//TODO: Do error handling
				throw exception
		}
	}

}
