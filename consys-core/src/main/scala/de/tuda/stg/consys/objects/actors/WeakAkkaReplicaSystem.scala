package de.tuda.stg.consys.objects.actors

import akka.actor.ActorRef
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.Weak
import de.tuda.stg.consys.objects.ConsistencyLevel
import de.tuda.stg.consys.objects.ConsistencyLevel.Weak
import de.tuda.stg.consys.objects.actors.Requests._
import de.tuda.stg.consys.objects.actors.WeakAkkaReplicaSystem.WeakReplicatedObject.{WeakFollowerReplicatedObject, WeakMasterReplicatedObject}

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
		extends WeakReplicatedObject[Addr, T]
		with AkkaMultiversionReplicatedObject[Addr, T] {
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

			override def handleRequest(request : Request) : Any = request match {
				case SynchronizeWithWeakMaster(ops) =>

					ops.foreach(op => {
						val before : List[String] = op.tx.locks.toList
						replicaSystem.setCurrentTransaction(op.tx)
						op match {
							case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
							case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
						}
						assert(replicaSystem.getCurrentTransaction.locks.toList == before)
						replicaSystem.clearTransaction()

					})

					WeakSynchronized(getObject)

				case _ =>
					super.handleRequest(request)
			}

			override def toString : String = s"WeakMaster($addr, $getObject)"

		}

		class WeakFollowerReplicatedObject[Addr, T <: AnyRef](
			init : T, val addr : Addr, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem[Addr]
		)(
			protected implicit val ttt : TypeTag[T]
		) extends WeakReplicatedObject[Addr, T] {
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
				val handler = replicaSystem.acquireHandlerFrom(masterReplica)

				val WeakSynchronized(newObj : T) =
					handler.request(addr, SynchronizeWithWeakMaster(unsynchronized))
				handler.close()

				setObject(newObj)
				unsynchronized.clear()
			}

			override def toString : String = s"WeakFollower($addr, $getObject)"
		}
	}

	sealed trait WeakReq extends Request
	case class SynchronizeWithWeakMaster(seq : scala.collection.Seq[Operation[_]]) extends WeakReq with ReturnRequest

	case class WeakSynchronized[T <: AnyRef](obj : T)

}

