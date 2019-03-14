package de.tudarmstadt.consistency.replobj.actors

import akka.actor.{ActorRef, Props}
import de.tudarmstadt.consistency.replobj.ConsistencyLevels
import de.tudarmstadt.consistency.replobj.ConsistencyLevels.Weak

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

	override protected def createMasterReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T, L] = {
		if (ConsistencyLevels.isWeak[L])
		//We have to cast here because the type system can not infer L == Strong
			new WeakMasterReplicatedObject[Addr, T](obj, addr, this).asInstanceOf[AkkaReplicatedObject[Addr, T, L]]
		else
			super.createMasterReplica[T, L](addr, obj)
	}

	override protected def createFollowerReplica[T <: AnyRef : TypeTag, L : TypeTag](addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T, L] = {
		if (ConsistencyLevels.isWeak[L])
		//We have to cast here because the type system can not infer L == Strong
			new WeakFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this).asInstanceOf[AkkaReplicatedObject[Addr, T, L]]
		else
			super.createFollowerReplica[T, L](addr, obj, masterRef)
	}
}

object WeakAkkaReplicaSystem {

	trait WeakReplicatedObject[Addr, T <: AnyRef] extends AkkaReplicatedObject[Addr, T, Weak]


	object WeakReplicatedObject {

		class WeakMasterReplicatedObject[Addr, T <: AnyRef](
	     init : T, val addr : Addr, val replicaSystem : AkkaReplicaSystem[Addr]
	  )(
	     protected implicit val ttt : TypeTag[T],
	     protected implicit val ltt : TypeTag[Weak]
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
//						replicaSystem.GlobalContext.set(_.push())
						replicaSystem.log(s"weak synchronize $op in context ${replicaSystem.GlobalContext.getCurrentPath}")

						op match {
							case InvokeOp(_, mthdName, args) => invoke(mthdName, args : _*)
							case SetFieldOp(_, fldName, newVal) => setField(fldName, newVal)
						}

					//							replicaSystem.request(addr, OpReq(op))

//						replicaSystem.GlobalContext.set(_.pop())
						replicaSystem.GlobalContext.resetContext()
					})

					WeakSynchronized(getObject)

				case _ =>
					super.handleRequest(request)
			}

		}

		class WeakFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T],
			protected implicit val ltt : TypeTag[Weak]
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

