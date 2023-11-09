package de.tuda.stg.consys.core.store.akkacluster.backend

import akka.actor.ExtendedActorSystem
import akka.cluster.ddata.Replicator._
import akka.cluster.ddata._
import akka.cluster.ddata.typed.scaladsl.Replicator
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter.{AddrType, CreateOrUpdateObject, MapType, ObjType, ReplKeyType, TransactionOp, ValueType}
import org.apache.curator.framework.CuratorFramework

import scala.concurrent.Await
import scala.concurrent.duration.FiniteDuration

object AkkaClusterReplicaAdapter {

	private type AddrType = String
	private type ObjType = Serializable

	private type ValueType = LWWRegister[Serializable]
	private type MapType = ORMap[String, ValueType]
	private type ReplKeyType = ORMapKey[AddrType, ValueType]


	sealed trait TransactionOp
	case class CreateOrUpdateObject(addr : AddrType, newState : ObjType) extends TransactionOp
}

//TODO: Implement support for mergeable objects.
class AkkaClusterReplicaAdapter(val system : ExtendedActorSystem, val curator : CuratorFramework, val timeout : FiniteDuration) {

	implicit val node: SelfUniqueAddress = DistributedData(system).selfUniqueAddress
	private val key : ReplKeyType = ORMapKey("consys-map")


	val replicator = DistributedData(system).replicator
	//Initial write of the object map
//	replicationActor.replicator ! Replicator.Update(ORMapKey("consys-map"), ORMap.empty[Addr, LWWRegister[ObjType]], WriteLocal) (ormap => ormap)


	def getAddress : akka.actor.Address =
		AkkaUtils.getActorSystemAddress(system)


	def writeLocal(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
		internalWrite(timestamp, ops, WriteLocal)
	}

	def writeAll(timestamp : Long, ops : Seq[TransactionOp]): Unit = {
		internalWrite(timestamp, ops, WriteAll(timeout))
	}

	//TODO: Incorporate timestamps in LWW registers
	private def internalWrite(timestamp : Long, ops : Seq[TransactionOp], consistency : WriteConsistency) : Unit = {
		replicator ! Replicator.Update(key, ORMap.empty, consistency) { ormap  =>
			var ormapTemp = ormap
			for (op <- ops) {
				op match {
					case CreateOrUpdateObject(addr, newState) =>
						ormapTemp = ormapTemp.asInstanceOf[MapType].updated(node, addr, LWWRegister.apply[AkkaStore#ObjType](node, newState)) { register =>
							register.withValue(node, newState)
						}
					case _ => throw new UnsupportedOperationException("transaction op unknown")
				}
			}
			ormapTemp
		}
	}

	def readLocal[T <: ObjType](addr : AddrType) : T = {
		internalRead(addr, ReadLocal)
	}

	def readAll[T <: ObjType](addr : AddrType) : T = {
		internalRead(addr, ReadAll(timeout))
	}

	private def internalRead[T <: ObjType](addr : AddrType, consistency : ReadConsistency) : T = {
		import akka.actor.typed.scaladsl.AskPattern._
		import akka.actor.typed.scaladsl.adapter._

		//TODO: Is the scheduler correct?
		val response = Askable(replicator).ask(Replicator.Get(key, consistency))(timeout, system.toTyped.scheduler)

		val result = Await.result(response, timeout)

		result match {
			case success : GetSuccess[MapType] =>
				success.dataValue.get(addr) match {
					case Some(LWWRegister(obj)) =>
						obj.asInstanceOf[T]
					case Some(_) =>
						???
					case None =>
						//TODO: Implement wait semantics?
						throw new IllegalArgumentException("key not available")
				}

			case notFound : NotFound[MapType] =>
				???

			case failure : GetFailure[MapType] =>
				???

			case deleted : GetDataDeleted[MapType] =>
				???

		}
	}

	def close() : Unit = {
		Await.ready(system.terminate(), timeout)
	}


}
