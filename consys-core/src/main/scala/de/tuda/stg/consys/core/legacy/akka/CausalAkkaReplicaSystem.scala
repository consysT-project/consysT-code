package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Causal
import de.tuda.stg.consys.core.legacy.akka.CausalAkkaReplicaSystem.CausalReplicatedObject.CausalMasterReplicatedObject
import de.tuda.stg.consys.core.legacy.akka.Requests._
import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._

trait CausalAkkaReplicaSystem extends AkkaReplicaSystem {

  override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
    case Causal => new CausalMasterReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createMasterReplica[T](l, addr, obj)
  }

  override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
    case Causal => new CausalMasterReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
  }

}

object CausalAkkaReplicaSystem {

  trait CausalReplicatedObject[Loc, T] extends AkkaReplicatedObject[Loc, T] {
    override final def consistencyLevel: ConsistencyLabel = Causal
  }

  object CausalReplicatedObject {

    class CausalMasterReplicatedObject[Loc, T](
      init: T, val addr: Loc, val replicaSystem: AkkaReplicaSystem {type Addr = Loc}
    )(
      protected implicit val ttt: TypeTag[T]
    )
      extends CausalReplicatedObject[Loc, T]
        with AkkaMultiversionReplicatedObject[Loc, T] {
      setObject(init)
      var messageQueue = new mutable.Queue[Message]
      var vc = VectorClock(replicaSystem.toString)

      override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]): R = {
        vc = vc.inc
        val result = super.internalInvoke[R](tx, methodName, args)
        replicaSystem.foreachOtherReplica(handler => {
          handler.request(addr, Message(vc, InvokeOp(tx, methodName, args)))})
        result
      }

      override def internalGetField[R](tx: Transaction, fldName: String): R = {
        vc = vc.inc
        val result = super.internalGetField[R](tx, fldName)
        replicaSystem.foreachOtherReplica(handler => {
          handler.request(addr, Message(vc, GetFieldOp(tx, fldName)))})
        result
      }

      override def internalSetField(tx: Transaction, fldName: String, newVal: Any): Unit = {
        vc = vc.inc
        super.internalSetField(tx, fldName, newVal)
        replicaSystem.foreachOtherReplica(handler => {
          internalSetField(tx, fldName, newVal)
          handler.request(addr, Message(vc, SetFieldOp(tx, fldName, newVal)))})
      }

      override def internalSync(): Unit = {

      }

      override def handleRequest[R](request: Request[R]): R = request match {
        case Message(senderVC, op) =>
          checkHappenedBefore(Message(senderVC, op))
          ().asInstanceOf[R]
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

        var headOpt = messageQueue.dequeueFirst(_ => true)
        while (headOpt.isDefined) {
          val head = headOpt.get
            if (head.senderVC happenedBefore vc) {
              head.op match {
                case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
                case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
                case GetFieldOp(tx, fldName) => internalGetField(tx, fldName)
              }
              vc = vc.merge(head.senderVC)
              headOpt = messageQueue.dequeueFirst(_ => true)
            } else
              return;
          }

      }

      override def toString: String = s"CausalMaster($addr, $getObject)"

    }


    case class Message (senderVC: VectorClock, op: Operation[_]) extends NoAnswerRequest

  }

}