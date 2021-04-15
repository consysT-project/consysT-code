package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.CmRDT
import de.tuda.stg.consys.core.legacy.akka.CmRDTAkkaReplicaSystem.CmRDTReplicatedObject
import de.tuda.stg.consys.core.legacy.akka.Requests.{InvokeOp, NoAnswerRequest, Operation, Request}
import scala.language.postfixOps
import scala.reflect.runtime.universe._

trait CmRDTAkkaReplicaSystem
  extends AkkaReplicaSystem
{
  override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match
  {
    case CmRDT => new CmRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createMasterReplica[T](l, addr, obj)
  }
  override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef): AkkaReplicatedObject[Addr, T] = l match
  {
    case CmRDT => new CmRDTReplicatedObject[Addr, T](obj, addr, this)
    case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
  }
}
object CmRDTAkkaReplicaSystem
{
  private case class RequestOperation(op : Operation[_]) extends NoAnswerRequest

  private [CmRDTAkkaReplicaSystem] class CmRDTReplicatedObject[Loc, T]
    (
      init : T, val addr : Loc, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
    )(
      protected implicit val ttt : TypeTag[T]
    ) extends AkkaReplicatedObject[Loc, T]
      with AkkaSECReplicatedObject[Loc, T]
      with Lockable[T]
  {
    setObject(init)

    override final def consistencyLevel : ConsistencyLevel = CmRDT

    override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R =
    {
      val invokeOp = InvokeOp(tx, methodName, args)
      val result : R = super.internalInvoke(tx, methodName, args)
      replicaSystem.foreachOtherReplica(handler =>
        {
          handler.request(addr, RequestOperation(invokeOp))
        })
      result
    }
    override def internalGetField[R](tx : Transaction, fldName : String) : R =
    {
      super.internalGetField(tx, fldName)
    }
    override def handleRequest[R](request : Request[R]) : R = request match
    {
      case RequestOperation(op) =>
        replicaSystem.setCurrentTransaction(op.tx)
        op match
        {
          case InvokeOp(tx, methodName, args) =>
            transactionStarted(tx)
            super.internalInvoke(tx, methodName, args)
            transactionFinished(tx) //Unlock all objects
          case _ =>
            throw new RuntimeException("Unknown op!")
        }
        replicaSystem.clearTransaction().asInstanceOf[R]
      case _ =>
        super.handleRequest(request)
    }
    override protected def transactionStarted(tx : Transaction) : Unit =
    {
      super.transactionStarted(tx)
    }
    override protected def transactionFinished(tx : Transaction) : Unit =
    {
      super.transactionFinished(tx)
    }
    override def toString : String = s"@CmRDT($addr, $getObject)"
  }
}
