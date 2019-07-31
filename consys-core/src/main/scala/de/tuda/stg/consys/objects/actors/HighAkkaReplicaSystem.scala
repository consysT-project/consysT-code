package de.tuda.stg.consys.objects.actors

import akka.actor.ActorRef
import akka.cluster.protobuf.msg.ClusterMessages.VectorClock
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.{High, Weak}
import de.tuda.stg.consys.objects.actors.HighAkkaReplicaSystem.HighReplicatedObject
import de.tuda.stg.consys.objects.actors.Requests.{GetFieldOp, InvokeOp, Operation, Request, ReturnRequest, SetFieldOp}
import de.tuda.stg.consys.objects.actors.WeakAkkaReplicaSystem.WeakReplicatedObject.{WeakFollowerReplicatedObject, WeakMasterReplicatedObject}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait HighAkkaReplicaSystem[Addr] extends AkkaReplicaSystem[Addr] {


	override protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case High => new HighReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case High => new HighReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}


object HighAkkaReplicaSystem {

	private case class SyncRequest(state : AnyRef, version : Long) extends Request with ReturnRequest


	private [HighAkkaReplicaSystem] class HighReplicatedObject[Addr, T <: AnyRef] (
    init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
  )(
    protected implicit val ttt : TypeTag[T]
  ) extends AkkaReplicatedObject[Addr, T] {
		setObject(init)

		override final def consistencyLevel : ConsistencyLevel = High

		private var version = Long.MinValue

		override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
			super.internalInvoke(tx, methodName, args)
		}

		override def internalGetField[R](tx : Transaction, fldName : String) : R = {
			super.internalGetField(tx, fldName)
		}

		override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
			super.internalSetField(tx, fldName, newVal)
		}

		override def internalSync() : Unit = {
			replicaSystem.foreachOtherReplica(handler => {
				val result = handler.request(addr, SyncRequest(getObject, version))
				result match {
					case None =>
					case Some((newObj : T@unchecked, newVersion : Long)) =>
						setObject(newObj.asInstanceOf[T])
						version = newVersion
				}
			})
		}

		override def handleRequest(request : Request) : Any = request match {
			case SyncRequest(syncObj, syncVersion) =>
				if (version < syncVersion) {
					setObject(syncObj.asInstanceOf[T])
					version = syncVersion
					None
				} else {
					Some((getObject, version))
				}

			case _ =>
				super.handleRequest(request)
		}

		override protected def transactionStarted(tx : Transaction) : Unit = {
			super.transactionStarted(tx)
		}

		override protected def transactionFinished(tx : Transaction) : Unit = {
			if (tx.isToplevel) {
				version = System.currentTimeMillis()
			}

			super.transactionFinished(tx)
		}

		override def toString : String = s"@High($addr, $getObject)"
	}


}


