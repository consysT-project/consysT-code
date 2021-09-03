package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.annotations.methods.WeakOp
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.{Mixed, Strong}
import de.tuda.stg.consys.core.legacy.akka.MixedAkkaReplicaSystem.MixedReplicatedObject.{MixedFollowerReplicatedObject, MixedMasterReplicatedObject}
import de.tuda.stg.consys.core.legacy.akka.Requests.{AsynchronousRequest, GetFieldOp, InvokeOp, NoAnswerRequest, Operation, Request, RequestHandler, SetFieldOp, SynchronousRequest}
import de.tuda.stg.consys.core.legacy.akka.StrongAkkaReplicaSystem.StrongReplicatedObject.{StrongFollowerReplicatedObject, StrongMasterReplicatedObject}
import jdk.dynalink.linker.support.TypeUtilities
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.DynamicVariable


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait MixedAkkaReplicaSystem extends AkkaReplicaSystem {

	override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Mixed => new MixedMasterReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Mixed => new MixedFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}


object MixedAkkaReplicaSystem {

	trait MixedReplicatedObject[Addr, T]
		extends AkkaReplicatedObject[Addr, T]
			with Lockable[T] {
		override final def consistencyLevel : ConsistencyLabel = Mixed

		def isWeak(methodName: String, args: Seq[Seq[Any]]) : Boolean = {
			ReflectiveAccess.resolveMethod(methodName, args) match {
				case Some(method) =>
					method.annotations.exists(annotation => annotation.toString.equals("de.tuda.stg.consys.annotations.methods.WeakOp"))
				case None =>
					println("method can not be resolved: " + methodName)
					false
			}
		}
	}


	object MixedReplicatedObject {

		class MixedMasterReplicatedObject[Loc, T](
			init : T, val addr : Loc, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
		)(
			protected implicit val ttt : TypeTag[T]
		) extends MixedReplicatedObject[Loc, T]
			with AkkaMultiversionReplicatedObject[Loc, T] {
			setObject(init)


			override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {

				if (isWeak(methodName, args)) {
					// Weak logic
					val res = super.internalInvoke[R](tx, methodName, args)
					this.replicaSystem.foreachOtherReplica(handler => handler.request(addr, WeakMergeReq(getObject)))
					res
				} else {
					// Strong logic
					if (opCache.contains(tx)) {
						//transaction is cached. No locking required.
					} else {
						lock(tx.id)
						tx.addLock(addr.asInstanceOf[String])
					}

					val res = super.internalInvoke[R](tx, methodName, args)
					res
				}



			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				throw new UnsupportedOperationException()
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				throw new UnsupportedOperationException()
			}

			override def internalSync() : Unit = {	}

			override def sync() : Unit = { }

			override protected def requiresCache(op : Operation[_]) : Boolean = {
//				!op.tx.hasOnlyLevel(Strong)
				false
			}

			override def handleRequest[R](request : Request[R]) : R = request match {
				case LockReq(txid) =>
					lock(txid)
					LockRes(getObject).asInstanceOf[R]

				case MergeReq(null, op, result) =>
					cache(op, result)
					().asInstanceOf[R]

				case MergeReq(newObj : T@unchecked, op, result) =>
					setObject(newObj)
					cache(op, result)
					().asInstanceOf[R]

				case UnlockReq(txid) =>
					unlock(txid)
					().asInstanceOf[R]

				case WeakMergeReq(obj) =>
					getObject.asInstanceOf[de.tuda.stg.consys.core.legacy.CanBeMerged[T]].merge(obj.asInstanceOf[T])
					().asInstanceOf[R]

				case _ => super.handleRequest(request)
			}

			override protected def transactionStarted(tx : Transaction) : Unit = {

				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				super.transactionFinished(tx)
			}

			override def toString : String = s"MixedMaster($addr, $getObject)"
		}


		class MixedFollowerReplicatedObject[Loc, T](
			init : T, val addr : Loc, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
		)(
			protected implicit val ttt : TypeTag[T]
		) extends MixedReplicatedObject[Loc, T]
			//TODO: Multiversion on follower? How to GC this?
			with AkkaMultiversionReplicatedObject[Loc, T] {
			setObject(init)

			//Handles communication with the master
			private var handler : DynamicVariable[RequestHandler[Loc]] = new DynamicVariable(null)

			override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				if (isWeak(methodName, args)) {
					// Weak logic
					val res = super.internalInvoke[R](tx, methodName, args)
					val answer = handler.value.request(addr, WeakMergeReq(getObject))
					res
				} else {
					// Strong logic
					if (opCache.contains(tx)) {
						//transaction is cached. No locking required.
					} else {
						lockWithHandler(tx.id, handler.value)
						tx.addLock(addr.asInstanceOf[String])
					}

					val res = super.internalInvoke[R](tx, methodName, args)
					handler.value.request(addr, MergeReq(getObject, InvokeOp(tx, methodName, args), res))
					res
				}
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				throw new UnsupportedOperationException()
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				throw new UnsupportedOperationException()
			}

			override def internalSync() : Unit = {
				val handler = replicaSystem.handlerFor(masterReplica)
				handler.request(addr, WeakMergeReq(getObject))
				handler.close()
			}



			override protected def requiresCache(op : Operation[_]) : Boolean = {
//				!op.tx.hasOnlyLevel(Strong)
				false
			}


			override private[akka] def lock(txid : Long) : Unit = {
				lockWithHandler(txid, replicaSystem.handlerFor(masterReplica))
			}

			override private[akka] def unlock(txid : Long) : Unit = {
				unlockWithHandler(txid, replicaSystem.handlerFor(masterReplica))
			}

			private def lockWithHandler(txid : Long, handler : RequestHandler[Loc]) : Unit = {
				val LockRes(masterObj : T@unchecked) = handler.request(addr, LockReq(txid))
				setObject(masterObj)
			}

			private def unlockWithHandler(txid : Long, handler : RequestHandler[Loc]) : Unit = {
				handler.request(addr, UnlockReq(txid))
			}

			override def toString : String = s"MixedFollower($addr, $getObject)"

			override def handleRequest[R](request : Request[R]) : R = request match {
				case WeakMergeReq(obj) =>
					getObject.asInstanceOf[de.tuda.stg.consys.core.legacy.CanBeMerged[T]].merge(obj.asInstanceOf[T])
					().asInstanceOf[R]

				case _ => super.handleRequest(request)
			}

			override protected def transactionStarted(tx : Transaction) : Unit = {
				assert(handler.value == null)
				handler.value = replicaSystem.handlerFor(masterReplica)
				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				handler.value.close()
				handler.value = null

				super.transactionFinished(tx)
			}
		}
	}



	case class SynchronizeWithWeakMaster(seq : scala.collection.Seq[Operation[_]]) extends SynchronousRequest[WeakSynchronized]
	case class WeakMergeReq(obj : Any) extends NoAnswerRequest
	case class WeakSynchronized(obj : Any)

	case class LockReq(txid : Long) extends SynchronousRequest[LockRes]
	case class LockRes(obj : Any)

	case class MergeReq(obj : Any, op : Operation[Any], result : Any) extends SynchronousRequest[Unit]
	case class UnlockReq(txid : Long) extends SynchronousRequest[Unit]

}

