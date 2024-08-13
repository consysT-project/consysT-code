package de.tuda.stg.consys.core.store.akkacluster.backend

import akka.actor.ExtendedActorSystem
import akka.cluster.ddata
import akka.cluster.ddata.Replicator._
import akka.cluster.ddata._
import akka.cluster.ddata.typed.scaladsl.Replicator.UpdateFailure
import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.core.store.akka.AkkaStore
import de.tuda.stg.consys.core.store.akka.utils.AkkaUtils
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter._
import de.tuda.stg.consys.logging.Logger
import org.apache.curator.framework.CuratorFramework

import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, TimeoutException}

object AkkaClusterReplicaAdapter {

	private type AddrType = String
	private type ObjType = Serializable

	private type ValueType = ReplicatedData
	private type MapType = ORMap[AddrType, ValueType]
	private type ReplKeyType = ORMapKey[String, ValueType]


	sealed trait TransactionOp
	case class CreateOrUpdateObject(addr : AddrType, newState : ObjType) extends TransactionOp
}

//TODO: Implement support for mergeable objects.
class AkkaClusterReplicaAdapter(val system : ExtendedActorSystem, val timeout : FiniteDuration) {

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

		val updateMessage = Replicator.Update.apply[MapType](key, ORMap.empty[AddrType, ValueType], consistency) { ormap =>
			var ormapTemp : MapType = ormap


			for (op <- ops) {

				op match {
					case CreateOrUpdateObject(addr, newState) =>

						newState match {

							case mergeable : Mergeable[_] =>
								ormapTemp = ormapTemp.updated(node, addr, MergeableReplicatedData(mergeable)) { replicatedData =>
									MergeableReplicatedData(mergeable)
								}

							case _ =>
								ormapTemp = ormapTemp.updated(node, addr, LWWRegister.apply[ObjType](node, newState)) { register =>
									register.asInstanceOf[LWWRegister[ObjType]].withValue(node, newState)
								}

						}


					case _ => throw new UnsupportedOperationException("transaction op unknown")
				}
			}
			ormapTemp
		}


		import akka.pattern._
		val response = replicator.ask(updateMessage)(timeout)
		val result = Await.result(response, timeout)

		result match {
			case UpdateSuccess(_, _) =>
				//Great!
			case UpdateFailure(_) =>
				Logger.err("update failed!")
			case UpdateTimeout =>
				Logger.err("update timeout!")
			case UpdateDataDeleted =>
				Logger.err("update data deleted")
		}

	}

	def readLocal[T <: ObjType](addr : AddrType) : T = {
		internalRead(addr, ReadLocal)
	}

	def readAll[T <: ObjType](addr : AddrType) : T = {
		internalRead(addr, ReadAll(timeout))
	}

	private def internalRead[T <: ObjType](addr : AddrType, consistency : ReadConsistency) : T = {


		val startTime = System.nanoTime()


		while (true) {
			val timeTaken = System.nanoTime() - startTime

			if (timeTaken > timeout.toNanos) {
				throw new TimeoutException(s"reference to $addr was not resolved")
			}

			import akka.pattern._
			val response = replicator.ask(Replicator.Get(key, consistency))(timeout)
			val result = Await.result(response, timeout)

			result match {
				case success : GetSuccess[MapType] =>
					success.dataValue.get(addr) match {
						case Some(LWWRegister(obj)) =>
							return obj.asInstanceOf[T]
						case Some(MergeableReplicatedData(obj)) =>
							return obj.asInstanceOf[T]
						case None =>
							//Key not available in the ormap. Retry until timeout.
//							throw new IllegalArgumentException("key not available")
//							Logger.err("AkkaClusterReplicaAdapter", "key not available yet")
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

		try {
			system.terminate()
			Await.ready(system.whenTerminated, timeout)
		} catch {
			case e : TimeoutException =>
				close()
		}

	}


}
