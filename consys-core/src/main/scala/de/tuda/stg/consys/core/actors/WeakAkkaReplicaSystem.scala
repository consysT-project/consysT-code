package de.tuda.stg.consys.core.actors

import akka.actor.ActorRef
import de.tuda.stg.consys.core.ConsistencyLevel
import de.tuda.stg.consys.core.ConsistencyLevel.Weak
import de.tuda.stg.consys.core.actors.Requests.{GetFieldOp, InvokeOp, Operation, Request, SetFieldOp, SynchronousRequest}
import de.tuda.stg.consys.core.actors.WeakAkkaReplicaSystem.WeakReplicatedObject.{WeakFollowerReplicatedObject, WeakMasterReplicatedObject}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait WeakAkkaReplicaSystem extends AkkaReplicaSystem {


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

	trait WeakReplicatedObject[Loc, T <: AnyRef] extends AkkaReplicatedObject[Loc, T] {
		override final def consistencyLevel : ConsistencyLevel = Weak
	}



	object WeakReplicatedObject {

		class WeakMasterReplicatedObject[Loc, T <: AnyRef](
	     init : T, val addr : Loc, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
	  )(
	     protected implicit val ttt : TypeTag[T]
	  )
		extends WeakReplicatedObject[Loc, T]
		with AkkaMultiversionReplicatedObject[Loc, T]
		{
			setObject(init)

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
				//super.internalSync()
			//	println("WARNING: sync on master")
			}

			override def handleRequest[R](request : Request[R]) : R = request match {
				case SynchronizeWithWeakMaster(ops) =>

					ops.foreach(op => {
						val before = op.tx.locks.toSet

						replicaSystem.setCurrentTransaction(op.tx)
						op match {
							case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
							case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
							case GetFieldOp(_, _) => throw new IllegalStateException("get field operations are not needed to be applied.")
						}

						assert(replicaSystem.getCurrentTransaction.locks.toSet == before)

						replicaSystem.clearTransaction()

					})

					WeakSynchronized[T](getObject).asInstanceOf[R]

				case _ =>
					super.handleRequest(request)
			}

			override def toString : String = s"WeakMaster($addr, $getObject)"

		}

		class WeakFollowerReplicatedObject[Loc, T <: AnyRef](
			init : T, val addr : Loc, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
		)(
			protected implicit val ttt : TypeTag[T]
		) extends WeakReplicatedObject[Loc, T] {
			setObject(init)

			private val unsynchronized : mutable.Buffer[Operation[_]] = mutable.Buffer.empty

			override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				unsynchronized += InvokeOp(tx, methodName, args)
				super.internalInvoke(tx, methodName, args)
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				super.internalGetField(tx, fldName)
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				unsynchronized += SetFieldOp(tx, fldName, newVal)
				super.internalSetField(tx, fldName, newVal)
			}


			override def internalSync() : Unit = {
				val handler = replicaSystem.handlerFor(masterReplica)

				val WeakSynchronized(newObj : T@unchecked) =
					handler.request(addr, SynchronizeWithWeakMaster[T](unsynchronized))
				handler.close()

				setObject(newObj)
				unsynchronized.clear()
			}

			override def toString : String = s"WeakFollower($addr, $getObject)"
		}
	}



	case class SynchronizeWithWeakMaster[T <: AnyRef](seq : scala.collection.Seq[Operation[_]]) extends SynchronousRequest[WeakSynchronized[T]]
	case class WeakSynchronized[T <: AnyRef](obj : T)



}

