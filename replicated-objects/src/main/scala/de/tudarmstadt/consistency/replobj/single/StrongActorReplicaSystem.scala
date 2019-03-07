package de.tudarmstadt.consistency.replobj.single

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem.{Request, ReturnRequest}
import de.tudarmstadt.consistency.replobj.single.StrongActorReplicaSystem.{InvokeReq, SetFieldReq, StrongReq}

import scala.reflect.runtime.universe._

/**
	* Created on 07.03.19.
	*
	* @author Mirko Köhler
	*/
trait StrongActorReplicaSystem[Addr] extends ActorReplicaSystem[Addr] {



	trait StrongReplicatedObject[T <: AnyRef, L] extends ActorReplicatedObject[T, L]


	class StrongReplicatedMasterObject[T <: AnyRef : TypeTag, L : TypeTag](val addr : Addr) extends StrongReplicatedObject[T, L] {

		override protected implicit def ttt : TypeTag[T] = implicitly[TypeTag[T]]
		override protected implicit def ltt : TypeTag[L] = implicitly[TypeTag[L]]

		override type Req = StrongReq

		override def handleRequest(request : StrongReq) : Option[Any] = request match {
			case SetFieldReq(fieldName, value) =>
				ReflectiveAccess.doSetField(fieldName, value)
				Some("ACK")
			case InvokeReq(methodName, args) =>
				ReflectiveAccess.doInvoke(methodName, args : _*)
		}

		override def getField[R](fieldName : String) : R =
			ReflectiveAccess.doGetField(fieldName)

		override def setField[R](fieldName : String, value : R) : Unit =
			request(addr, SetFieldReq(fieldName, value))

		override def invoke[R](methodName : String, args : Any*) : R =
			request(addr, InvokeReq(methodName, args)).get.asInstanceOf[R]

		override def sync() : Unit =
			throw new UnsupportedOperationException("synchronize on strong consistent object")
	}


	class StrongReplicatedFollowerObject[T <: AnyRef : TypeTag, L : TypeTag](val addr : Addr, val masterReplica : ActorRef) extends StrongReplicatedObject[T, L] {

		override protected implicit def ttt : TypeTag[T] = implicitly[TypeTag[T]]
		override protected implicit def ltt : TypeTag[L] = implicitly[TypeTag[L]]

		override type Req = StrongReq

		override def handleRequest(request : StrongReq) : Option[Any] = request match {
			case SetFieldReq(fieldName, value) =>
				ReflectiveAccess.doSetField(fieldName, value)
				Some("ACK")
			case InvokeReq(methodName, args) =>
				ReflectiveAccess.doInvoke(methodName, args : _*)
		}

		override def getField[R](fieldName : String) : R =
			ReflectiveAccess.doGetField(fieldName)

		override def setField[R](fieldName : String, value : R) : Unit =
			request(addr, SetFieldReq(fieldName, value))

		override def invoke[R](methodName : String, args : Any*) : R =
			request(addr, InvokeReq(methodName, args)).get.asInstanceOf[R]

		override def sync() : Unit =
			throw new UnsupportedOperationException("synchronize on strong consistent object")
	}
}

object StrongActorReplicaSystem {

	private sealed trait StrongReq extends Request
	private case class SetFieldReq(fieldName : String, newVal : Any) extends StrongReq with ReturnRequest
	private case class InvokeReq(methodName : String, args : Seq[Any]) extends StrongReq with ReturnRequest
	private case class GetFieldReq(fieldName : String) extends StrongReq with ReturnRequest
	private case object SynchronizeReq extends StrongReq with ReturnRequest
	private case class SynchronizeResponse[T <: AnyRef](obj : T) extends StrongReq with ReturnRequest



	private case object LockReq extends StrongReq
	private case object LockRes extends StrongReq
	private case class MergeAndUnlock(obj : AnyRef) extends StrongReq
	private case object SynchronizeReq extends StrongReq
	private case class SynchronizeRes(obj : AnyRef) extends StrongReq

}
