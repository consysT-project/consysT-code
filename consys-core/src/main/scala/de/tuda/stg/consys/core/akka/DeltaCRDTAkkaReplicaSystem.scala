package de.tuda.stg.consys.core.akka
import java.io

import akka.actor.{ActorRef, ActorSystem}
import de.tuda.stg.consys.core.Address

import scala.reflect.runtime.universe._
import de.tuda.stg.consys.core.akka.DeltaCRDTAkkaReplicaSystem.{DeltaCRDTReplicatedObject, DeltaUpdateReq}
import de.tuda.stg.consys.core.ConsistencyLabel.DCRDT
import de.tuda.stg.consys.core.akka.Requests.{InvokeOp, NoAnswerRequest, Operation, Request, SynchronousRequest}

import scala.concurrent.duration.FiniteDuration
import scala.reflect.runtime.universe
/*
Author: Kris Frühwein und Julius Näumann
 */
trait DeltaCRDTAkkaReplicaSystem extends AkkaReplicaSystem {



  override protected def createMasterReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T): AkkaReplicatedObject[Addr, T] = {
    val result = l match {

      case DCRDT => new DeltaCRDTReplicatedObject[Addr, T](obj, addr, this)
      case _ => super.createMasterReplica[T](l, addr, obj)
    }
    println("created master replica")
    result
  }

  override protected def createFollowerReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T, masterRef: ActorRef): AkkaReplicatedObject[Addr, T] = {
    val result = l match {
      case DCRDT => new DeltaCRDTReplicatedObject[Addr, T](obj, addr, this)
      case _ => super.createFollowerReplica[T](l, addr, obj, masterRef)
    }
    println("created follower replicas")
    result
  }
}
/*
  object DeltaCRDTAkkaReplicatedObject {

    trait DeltaCRDTReplicatedObject[Addr, T]
      extends AkkaReplicatedObject[Addr, T]
        with Lockable[T] {

    }
*/

trait DeltaHandler {
  def transmitDelta(delta: Any)
}

    object DeltaCRDTAkkaReplicaSystem {

      private case class RequestOperation(op: Operation[_]) extends SynchronousRequest[Unit]

      private case class RequestSync(tx: Transaction) extends SynchronousRequest[Unit]

      case class Message(obj: Any) extends NoAnswerRequest

      case class DeltaUpdateReq(obj: Any) extends NoAnswerRequest



      class DeltaCRDTReplicatedObject[Loc, T]
      (
        init: T, val addr: Loc, val replicaSystem: AkkaReplicaSystem {type Addr = Loc}
      )(
        protected implicit val ttt: TypeTag[T]
      ) extends AkkaSECReplicatedObject[Loc, T]
        with Lockable[T]
        with Serializable
        with DeltaHandler
      {
        setObject(init)
        val t = init.asInstanceOf[DeltaCRDT]

        override final def consistencyLevel: ConsistencyLevel = DCRDT

        override def handleRequest[R](request: Request[R]): R = request match {
          case DeltaUpdateReq(state: AkkaReplicaSystem#Obj) =>
            getObject.asInstanceOf[DeltaCRDT].merge(state)

            None.asInstanceOf[R]
          case _ =>
            super.handleRequest(request)

        }

        override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]): R = {
          val result = super.internalInvoke[R](tx, methodName, args)
          if (result.isInstanceOf[Delta]) {
            val d = result.asInstanceOf[Delta]
            replicaSystem.foreachOtherReplica(handler => handler.request(addr, DeltaUpdateReq(d.delta)))
          }
          result
        }



        override def sync(): Unit = {
          // todo:
          // traditional sync method does not make sense in the context of dcrdt
          // should there be an option to force sync?
          println(s"DCRDT '$addr' sync")
        }

        override protected def transactionStarted(tx: Transaction): Unit = {
          super.transactionStarted(tx)
        }

        override protected def transactionFinished(tx: Transaction): Unit = {
          super.transactionFinished(tx)
        }

        override def toString: String = s"@DCRDT($addr, $getObject)"

        override def transmitDelta(delta: Any): Unit = {
          replicaSystem.foreachOtherReplica(handler => handler.request(addr, DeltaUpdateReq(delta)))
        }
      }
    }

abstract class DeltaCRDT extends DeltaMergeable {

}

class Delta (
  d: AkkaReplicaSystem#Obj
  )  {
    var delta :AkkaReplicaSystem#Obj = d
  }

class ResultWrapper[T <: Object] (v: T, d: AkkaReplicaSystem#Obj)
extends Delta(d) {
  val value: T = v
}



