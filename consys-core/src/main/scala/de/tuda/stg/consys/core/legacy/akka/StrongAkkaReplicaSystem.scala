package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Strong
import de.tuda.stg.consys.core.legacy.akka.Requests._
import de.tuda.stg.consys.core.legacy.akka.StrongAkkaReplicaSystem.StrongReplicatedObject.{StrongFollowerReplicatedObject, StrongMasterReplicatedObject}
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.DynamicVariable


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait StrongAkkaReplicaSystem extends AkkaReplicaSystem {

	override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Strong => new StrongMasterReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Strong => new StrongFollowerReplicatedObject[Addr, T](obj, addr, masterRef, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}

object StrongAkkaReplicaSystem {

	trait StrongReplicatedObject[Addr, T]
		extends AkkaReplicatedObject[Addr, T]
		with Lockable[T] {
		override final def consistencyLevel : ConsistencyLabel = Strong
	}

	object StrongReplicatedObject {

		class StrongMasterReplicatedObject[Loc, T](
			init : T, val addr : Loc, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Loc, T]
			with AkkaMultiversionReplicatedObject[Loc, T] {
			setObject(init)

			override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				val result = super.internalInvoke[R](tx, methodName, args)
				result
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				val result = super.internalGetField[R](tx, fldName)
				result
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(tx, fldName, newVal)
			}

			override def internalSync() : Unit = {	}

			override def sync() : Unit = { }

			override protected def requiresCache(op : Operation[_]) : Boolean = {
				!op.tx.hasOnlyLevel(Strong)
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

				case _ => super.handleRequest(request)
			}

			override protected def transactionStarted(tx : Transaction) : Unit = {
				if (opCache.contains(tx)) {
					//transaction is cached. No locking required.
				} else {
					lock(tx.id)
					tx.addLock(addr.asInstanceOf[String])
				}
				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				super.transactionFinished(tx)
			}

			override def toString : String = s"StrongMaster($addr, $getObject)"
		}


		class StrongFollowerReplicatedObject[Loc, T](
			init : T, val addr : Loc, val masterReplica : ActorRef, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
		)(
			protected implicit val ttt : TypeTag[T]
		) extends StrongReplicatedObject[Loc, T]
			//TODO: Multiversion on follower? How to GC this?
			with AkkaMultiversionReplicatedObject[Loc, T] {
			setObject(init)

			//Handles communication with the master
			private var handler : DynamicVariable[RequestHandler[Loc]] = new DynamicVariable(null)

			override def internalInvoke[R](tx: Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
				val res = super.internalInvoke[R](tx, methodName, args)
				handler.value.request(addr, MergeReq(getObject, InvokeOp(tx, methodName, args), res))

				res
			}

			override def internalGetField[R](tx : Transaction, fldName : String) : R = {
				val res = super.internalGetField[R](tx, fldName)
				handler.value.request(addr,  MergeReq(null, GetFieldOp(tx, fldName), res))

				res
			}

			override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
				super.internalSetField(tx, fldName, newVal)
				handler.value.request(addr, MergeReq(getObject, SetFieldOp(tx, fldName, newVal), ()))
			}

			override def internalSync() : Unit = {	}

			override def sync() : Unit = { }


			override protected def requiresCache(op : Operation[_]) : Boolean = {
				!op.tx.hasOnlyLevel(Strong)
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

			override def toString : String = s"StrongFollower($addr, $getObject)"


			override protected def transactionStarted(tx : Transaction) : Unit = {
				assert(handler.value == null)

				handler.value = replicaSystem.handlerFor(masterReplica)

				if (opCache.contains(tx)) {
					//transaction is cached. No locking required.
				} else {
					lockWithHandler(tx.id, handler.value)
					tx.addLock(addr.asInstanceOf[String])
				}

				super.transactionStarted(tx)
			}

			override protected def transactionFinished(tx : Transaction) : Unit = {
				handler.value.close()
				handler.value = null

				super.transactionFinished(tx)
			}



		}
	}



	case class LockReq(txid : Long) extends SynchronousRequest[LockRes]
	case class LockRes(obj : Any)

	case class MergeReq(obj : Any, op : Operation[Any], result : Any) extends SynchronousRequest[Unit]
	case class UnlockReq(txid : Long) extends SynchronousRequest[Unit]

}
