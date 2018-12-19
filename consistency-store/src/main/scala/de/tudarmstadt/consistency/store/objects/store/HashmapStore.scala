package de.tudarmstadt.consistency.store.objects.store

import de.tudarmstadt.consistency.store.objects.DistributedObjectLanguage

import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait HashmapStore extends Store {
	self : DistributedObjectLanguage =>

	val data : mutable.Map[OpId, Operation] = mutable.HashMap.empty
	val sessions : mutable.MultiMap[B#Address, Operation] = new mutable.HashMap[B#Address, mutable.Set[Operation]] with mutable.MultiMap[B#Address, Operation]


	override def addOperation(op : Operation) : Try[Unit] = synchronized {
		op.opType match {
			case EnrefOp if !data.contains(op.id) =>
				data.put(op.id, op)
				sessions.addBinding(op.addr, op)
				Success()
			case UpdateOp if data.contains(op.id) =>
				data.put(op.id, op)
				sessions.addBinding(op.addr, op)
				Success()
			case _ =>
				Failure(new IllegalStateException(s"cannot execute operation $op"))
		}
	}

	override def read(addr : B#Address) : Try[Set[Operation]] = synchronized {
		Success(sessions.getOrElse(addr, Set.empty).toSet)
	}


}
