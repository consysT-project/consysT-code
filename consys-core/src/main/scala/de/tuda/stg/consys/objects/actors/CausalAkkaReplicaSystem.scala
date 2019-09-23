package de.tuda.stg.consys.objects.actors

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.Causal
import de.tuda.stg.consys.objects.actors.Requests._
import de.tuda.stg.consys.objects.actors.CausalAkkaReplicaSystem.CausalReplicatedObject.CausalMasterReplicatedObject

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.control.Breaks.{break, breakable}

trait CausalAkkaReplicaSystem[Addr] extends AkkaReplicaSystem[Addr] {

  override protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
    case Causal => new CausalMasterReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createMasterReplica[T](l, addr, obj)
  }

  override protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
    case Causal => new CausalMasterReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
  }

}

object CausalAkkaReplicaSystem {

  trait CausalReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T] {
    override final def consistencyLevel: ConsistencyLevel = Causal
  }

  object CausalReplicatedObject {

    class CausalMasterReplicatedObject[Addr, T <: AnyRef](init: T, val addr: Addr, val replicaSystem: AkkaReplicaSystem[Addr]
                                                         )(
                                                           protected implicit val ttt: TypeTag[T]
                                                         )
      extends CausalReplicatedObject[Addr, T]
        with AkkaMultiversionReplicatedObject[Addr, T] {
      setObject(init)
      var messageQueue = new mutable.Queue[Message]
      var vc = VectorClock(replicaSystem.toString)
      override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]): R = {
        vc = vc.inc
        val result = super.internalInvoke(tx, methodName, args)
        replicaSystem.foreachOtherReplica(handler => {
          handler.request(addr, Message(vc, InvokeOp(tx, methodName, args)))})
        result
      }

      override def internalGetField[R](tx: Transaction, fldName: String): R = {
        vc = vc.inc
        val result = super.internalGetField(tx, fldName)
        replicaSystem.foreachOtherReplica(handler => {
          handler.request(addr, Message(vc, internalGetField(tx, fldName)))})
        result
      }

      override def internalSetField(tx: Transaction, fldName: String, newVal: Any): Unit = {
        vc = vc.inc
        super.internalSetField(tx, fldName, newVal)
        replicaSystem.foreachOtherReplica(handler => {
          internalSetField(tx, fldName, newVal)
          handler.request(addr, Message(vc, internalGetField(tx, fldName)))})
      }

      override def internalSync(): Unit = {

      }

      override def handleRequest(request: Request): Any = request match {
        case Message(senderVC, op) => checkHappenedBefore(Message(senderVC, op))
        case _ => super.handleRequest(request)
      }

      def checkHappenedBefore(currentMessage: Message): Unit = {
        if (!(currentMessage.senderVC happenedBefore vc)) {
          messageQueue += currentMessage
        } else {
          currentMessage.op match {
            case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
            case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
            case GetFieldOp(tx, fldName) => internalGetField(tx, fldName)
          }
          vc = vc.merge(currentMessage.senderVC)
        }
        checkMessageQueue()
      }

      def checkMessageQueue(): Unit = {
        breakable {
          while (messageQueue.nonEmpty) {
            if (messageQueue.head.senderVC happenedBefore vc) {
              messageQueue.head.op match {
                case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
                case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
                case GetFieldOp(tx, fldName) => internalGetField(tx, fldName)
              }
              vc = vc.merge(messageQueue.head.senderVC)
              messageQueue.dequeue()
            } else
              break
          }
        }
      }

      override def toString: String = s"CausalMaster($addr, $getObject)"

    }


    sealed trait CausalReq extends Request
    case class Message (senderVC: VectorClock, op: Operation[_]) extends Request with NonReturnRequest

  }

}