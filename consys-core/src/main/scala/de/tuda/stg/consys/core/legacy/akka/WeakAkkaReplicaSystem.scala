package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Weak
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystemFactory.AkkaReplicaSystemBinding
import de.tuda.stg.consys.core.legacy.akka.Requests._
import de.tuda.stg.consys.core.legacy.akka.WeakAkkaReplicaSystem.WeakReplicatedObject.{WeakFollowerReplicatedObject, WeakMasterReplicatedObject}
import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait WeakAkkaReplicaSystem extends AkkaReplicaSystem {


	override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Weak => new WeakMasterReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Weak => new WeakFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}

object WeakAkkaReplicaSystem {

	trait WeakReplicatedObject[Loc, T] extends AkkaReplicatedObject[Loc, T] {
		override final def consistencyLevel : ConsistencyLabel = Weak
	}

	object WeakReplicatedObject {

		class WeakMasterReplicatedObject[Loc, T](
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
						AkkaReplicaSystems.withValue(replicaSystem.asInstanceOf[AkkaReplicaSystemBinding]) {
							ops.foreach(op => {
								val before = op.tx.locks.toSet

								replicaSystem.setCurrentTransaction(op.tx)
								op match {
									case InvokeOp(path, mthdName, args) => internalInvoke[Any](path, mthdName, args)
									case SetFieldOp(path, fldName, newVal) => internalSetField(path, fldName, newVal)
									case x => throw new IllegalStateException(s"Cannot apply operation ${x}")
								}

								assert(replicaSystem.getCurrentTransaction.locks.toSet == before)

								replicaSystem.clearTransaction()
							})
						}

						WeakSynchronized(getObject).asInstanceOf[R]

					case _ =>
						super.handleRequest(request)

			}

			override def toString : String = s"WeakMaster($addr, $getObject)"

		}

		class WeakFollowerReplicatedObject[Loc, T](
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
					handler.request(addr, SynchronizeWithWeakMaster(unsynchronized))
				handler.close()

				setObject(newObj)
				unsynchronized.clear()
			}

			override def toString : String = s"WeakFollower($addr, $getObject)"
		}
	}



	case class SynchronizeWithWeakMaster(seq : scala.collection.Seq[Operation[_]]) extends SynchronousRequest[WeakSynchronized]
	case class WeakSynchronized(obj : Any)



}

