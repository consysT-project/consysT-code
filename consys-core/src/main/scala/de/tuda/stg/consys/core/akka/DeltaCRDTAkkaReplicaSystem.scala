package de.tuda.stg.consys.core.akka
import java.io

import akka.actor.ActorSystem
import scala.reflect.runtime.universe._
import de.tuda.stg.consys.core.akka.DeltaCRDTAkkaReplicaSystem.DeltaCRDTReplicatedObject
import de.tuda.stg.consys.core.ConsistencyLabel.DCRDT
import de.tuda.stg.consys.core.akka.Requests.{InvokeOp, NoAnswerRequest, Operation, Request, SynchronousRequest}

import scala.concurrent.duration.FiniteDuration
import scala.reflect.runtime.universe
/*
Author: Kris Frühwein und Julius Näumann
 */
trait DeltaCRDTAkkaReplicaSystem extends AkkaReplicaSystem {

  override protected def createMasterReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T): AkkaReplicatedObject[Addr, T] = l match {
    case DCRDT => new DeltaCRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ => super.createMasterReplica[T](l, addr, obj)
  }

  override protected def createFollowerReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T, masterRef: ActorRef): AkkaReplicatedObject[Addr, T] = l match {
    case DCRDT => new DeltaCRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ => super.createFollowerReplica[T](l, addr, obj, masterRef)
  }
}
/*
  object DeltaCRDTAkkaReplicatedObject {

    trait DeltaCRDTReplicatedObject[Addr, T]
      extends AkkaReplicatedObject[Addr, T]
        with Lockable[T] {

    }
*/

    object DeltaCRDTAkkaReplicaSystem {

      private case class RequestOperation(op: Operation[_]) extends SynchronousRequest[Unit]

      private case class RequestSync(tx: Transaction) extends SynchronousRequest[Unit]

      case class Message(obj: Any) extends NoAnswerRequest

      case class DeltaUpdateReq(obj: Any) extends NoAnswerRequest


      private[DeltaCRDTAkkaReplicaSystem] class DeltaCRDTReplicatedObject[Loc, T <: DeltaMergeable[T]]
      (
        init: T, val addr: Loc, val replicaSystem: AkkaReplicaSystem {type Addr = Loc}
      )(
        protected implicit val ttt: TypeTag[T]
      ) extends AkkaSECReplicatedObject[Loc, T]
        with Lockable[T]
        with Serializable {
        setObject(init)

        override final def consistencyLevel: ConsistencyLevel = DCRDT

        override def handleRequest[R](request: Request[R]): R = request match {
          case DeltaUpdateReq(state: DeltaMergeable[T]#DeltaType@unchecked) =>
            getObject.asInstanceOf[DeltaMergeable[T]].merge(state)
            None.asInstanceOf[R]
          case _ =>
            super.handleRequest(request)

        }

        override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]): R = {
          val result = super.internalInvoke[R](tx, methodName, args)
          replicaSystem.foreachOtherReplica(handler => handler.request(addr, DeltaUpdateReq(getObject)))
          result
        }

        override protected def transactionStarted(tx: Transaction): Unit = {
          super.transactionStarted(tx)
        }

        override protected def transactionFinished(tx: Transaction): Unit = {
          super.transactionFinished(tx)
        }

        override def toString: String = s"@DCRDT($addr, $getObject)"

      }
    }
