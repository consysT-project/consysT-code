package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.CvRDT
import de.tuda.stg.consys.core.legacy.akka.CvRDTAkkaReplicaSystem.CvRDTReplicatedObject
import de.tuda.stg.consys.core.legacy.akka.Requests.{NoAnswerRequest, Operation, Request, SynchronousRequest}
import scala.language.postfixOps
import scala.reflect.runtime.universe._


trait CvRDTAkkaReplicaSystem
  extends AkkaReplicaSystem {
  override protected def createMasterReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T): AkkaReplicatedObject[Addr, T] = l match {
    case CvRDT => new CvRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ => super.createMasterReplica[T](l, addr, obj)
  }

  override protected def createFollowerReplica[T <: Obj : TypeTag](l: ConsistencyLevel, addr: Addr, obj: T, masterRef: ActorRef): AkkaReplicatedObject[Addr, T] = l match {
    case CvRDT => new CvRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ => super.createFollowerReplica[T](l, addr, obj, masterRef)
  }
}

object CvRDTAkkaReplicaSystem {

  private case class RequestOperation(op: Operation[_]) extends SynchronousRequest[Unit]

  private case class RequestSync(tx: Transaction) extends SynchronousRequest[Unit]

  case class Message(obj: Any) extends NoAnswerRequest

  case class UpdateReq(obj: Any) extends NoAnswerRequest


  private[CvRDTAkkaReplicaSystem] class CvRDTReplicatedObject[Loc, T]
  (
    init: T, val addr: Loc, val replicaSystem: AkkaReplicaSystem {type Addr = Loc}
  )(
    protected implicit val ttt: TypeTag[T]
  ) extends AkkaSECReplicatedObject[Loc, T]
    with Lockable[T]
    with Serializable {
    setObject(init)

    override final def consistencyLevel: ConsistencyLevel = CvRDT

    override def handleRequest[R](request: Request[R]): R = request match {
      case UpdateReq(state: T@unchecked) =>
        getObject.asInstanceOf[Mergeable[Any]].merge(state)
        None.asInstanceOf[R]
      case _ =>
        super.handleRequest(request)
    }

    override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]): R = {
      val result = super.internalInvoke[R](tx, methodName, args)
      replicaSystem.foreachOtherReplica(handler => handler.request(addr, UpdateReq(getObject)))
      result
    }

    override protected def transactionStarted(tx: Transaction): Unit = {
      super.transactionStarted(tx)
    }

    override protected def transactionFinished(tx: Transaction): Unit = {
      super.transactionFinished(tx)
    }

    override def toString: String = s"@CvRDT($addr, $getObject)"

  }

}


