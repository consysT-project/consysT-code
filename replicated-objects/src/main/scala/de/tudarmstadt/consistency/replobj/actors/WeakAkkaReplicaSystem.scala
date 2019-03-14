package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import de.tudarmstadt.consistency.replobj.ConsistencyLevel
import de.tudarmstadt.consistency.replobj.ConsistencyLevel.Weak
import de.tudarmstadt.consistency.replobj.actors.Requests._
import de.tudarmstadt.consistency.replobj.actors.WeakAkkaReplicaSystem.WeakReplicatedObject.{WeakFollowerReplicatedObject, WeakMasterReplicatedObject}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait WeakAkkaReplicaSystem[Addr] extends AkkaReplicaSystem[Addr] {


	override protected def createMasterReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Weak => new WeakMasterReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: AnyRef : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Weak => new WeakFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}

object WeakAkkaReplicaSystem {

	trait WeakReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T] {
		override final def consistencyLevel : ConsistencyLevel = Weak
	}


	object WeakReplicatedObject {

		class WeakMasterReplicatedObject[Addr, T <: AnyRef](
	     init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
	  )(
	     protected implicit val ttt : TypeTag[T]
	  )
		extends WeakReplicatedObject[Addr, T] {
			setObject(init)

			protected override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				super.internalInvoke(opid, methodName, args)
			}

			override protected def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				super.internalGetField(opid, fldName)
			}

			override protected def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(opid, fldName, newVal)
			}

			override protected def internalSync() : Unit = {
				super.internalSync()
			}

			override def handleRequest(request : Request) : Any = request match {
				case SynchronizeWithWeakMaster(ops) =>

					ops.foreach(op => {
						replicaSystem.GlobalContext.setContext(op.path)
						replicaSystem.log(s"weak synchronize $op in context ${replicaSystem.GlobalContext.getBuilder.getParentPath}")

						op match {
							case InvokeOp(path, mthdName, args) => internalInvoke(path, mthdName, args)
							case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
						}

						replicaSystem.GlobalContext.resetBuilder()
					})

					WeakSynchronized(getObject)

				case _ =>
					super.handleRequest(request)
			}

		}

		class WeakFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends WeakReplicatedObject[Addr, T] {
			setObject(init)


			private val unsynchronized : mutable.Buffer[Operation[_]] = mutable.Buffer.empty


			protected override def internalInvoke[R](opid: ContextPath, methodName: String, args: Seq[Any]) : R = {
				unsynchronized += InvokeOp(opid, methodName, args)
				super.internalInvoke(opid, methodName, args)
			}

			override protected def internalGetField[R](opid : ContextPath, fldName : String) : R = {
				super.internalGetField(opid, fldName)
			}

			override protected def internalSetField(opid : ContextPath, fldName : String, newVal : Any) : Unit = {
				unsynchronized += SetFieldOp(opid, fldName, newVal)
				super.internalSetField(opid, fldName, newVal)
			}


			override protected def internalSync() : Unit = {
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val WeakSynchronized(newObj : T) = handler.request(addr, SynchronizeWithWeakMaster(unsynchronized))
				handler.close()

				setObject(newObj)
				unsynchronized.clear()
			}
		}
	}

	private sealed trait WeakReq extends Request
	private case class SynchronizeWithWeakMaster(seq : Seq[Operation[_]]) extends WeakReq with ReturnRequest

	private case class WeakSynchronized[T <: AnyRef](obj : T)

}

