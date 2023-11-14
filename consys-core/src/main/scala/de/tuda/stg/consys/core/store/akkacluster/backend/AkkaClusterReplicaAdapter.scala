package de.tuda.stg.consys.core.store.akkacluster.backend

import akka.actor.ExtendedActorSystem
import akka.cluster.ddata.Replicator._
import akka.cluster.ddata._
import akka.cluster.ddata.typed.scaladsl.Replicator
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.backend.AkkaObject
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter.ReadObject
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter.{AddrType, CreateOrUpdateObject, MapType, ObjType, ReplKeyType, TransactionOp, ValueType}
import de.tuda.stg.consys.logging.Logger
import org.apache.curator.framework.CuratorFramework

import java.util.concurrent.TimeUnit
import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration.FiniteDuration
import scala.util.Try

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
	node.hashCode()
	val key : ReplKeyType = ORMapKey("consys-map")


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


		val startTime = System.nanoTime()


		while (true) {
			val timeTaken = System.nanoTime() - startTime

			if (timeTaken > timeout.toNanos) {
				throw new TimeoutException(s"reference to $addr was not resolved")
			}


			//TODO: Is the scheduler correct?
			val response = Askable(replicator).ask(Replicator.Get(key, consistency))(timeout, system.toTyped.scheduler)
			val result = Await.result(response, timeout)

			result match {
				case success : GetSuccess[MapType] =>
					success.dataValue.get(addr) match {
						case Some(LWWRegister(obj)) =>
							return obj.asInstanceOf[T]
						case Some(_) =>
							//TODO: Implement mergeable data types
							???
						case None =>
//							throw new IllegalArgumentException("key not available")
							Logger.err("AkkaClusterReplicaAdapter", "key not available yet")
					}

				case notFound : NotFound[MapType] =>
					Logger.err("AkkaClusterReplicaAdapter", "ormap not found")

				case failure : GetFailure[MapType] =>
					Logger.err("AkkaClusterReplicaAdapter", "failed to read ormap")

				case deleted : GetDataDeleted[MapType] =>
					throw new IllegalArgumentException("ormap was deleted")

			}

			Thread.sleep(100)
		}

		throw new RuntimeException()
	}

	def close() : Unit = {
		Await.ready(system.terminate(), timeout)
	}


}
