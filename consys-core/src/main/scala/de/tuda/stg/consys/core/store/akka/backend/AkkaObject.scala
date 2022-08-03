package de.tuda.stg.consys.core.store.akka.backend

import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.{Addr, Level, ObjType}

import scala.reflect.ClassTag

private[backend] abstract class AkkaObject[T <: ObjType : ClassTag] extends Serializable {
	def addr : Addr
	def state : T
	def level : Level

	/* TODO: Change to immutable objects */
	def mergeWith(otherState : T, timestamp : Long) : Unit
}

private[backend] case class DefaultAkkaObject[T <: ObjType : ClassTag](
	override val addr : Addr,
	var mutableState : T,
	override val level : Level,
	var lastChanged : Long
) extends AkkaObject[T] {

	@inline def state : T = mutableState

	def mergeWith(otherState : T, timestamp : Long) : Unit = {
		if (timestamp > lastChanged) {
			mutableState = otherState
			lastChanged = timestamp
		}
	}
}

private[backend] case class MergeableAkkaObject[T <: ObjType : ClassTag](
	override val addr : Addr,
	override val state : T,
	override val level : Level
) extends AkkaObject[T] {
	require(state.isInstanceOf[Mergeable[T]])

	override def mergeWith(otherState : T, timestamp : Long) : Unit = {
		state.asInstanceOf[Mergeable[T]].merge(otherState)
	}
}

private[backend] object AkkaObject {
	def create[T <: Serializable : ClassTag](addr : Addr, state : T, level : Level, timestamp : Long) : AkkaObject[T] = {
		if (state.isInstanceOf[Mergeable[T]])
			MergeableAkkaObject(addr, state.asInstanceOf[T with Mergeable[T] with ObjType], level).asInstanceOf[AkkaObject[T]]
		else
			DefaultAkkaObject(addr, state, level, timestamp)
	}
}
