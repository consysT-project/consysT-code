package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Low
import de.tuda.stg.consys.core.legacy.akka.LowAkkaReplicaSystem.LowReplicatedObject
import de.tuda.stg.consys.core.legacy.akka.Requests._
import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.{DynamicVariable, Random}


/**
	*
	* @author Mirko Köhler
	*/
/* FIXME: This implementation is not working completely yet, as concurrent execution leads to deadlocks. */
trait LowAkkaReplicaSystem extends AkkaReplicaSystem {


	override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Low => new LowReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Low => new LowReplicatedObject[Addr, T](obj, addr, this)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}


object LowAkkaReplicaSystem {

	private case class LockRequest(txid : Long) extends SynchronousRequest[Boolean]
	private case class UnlockRequest(txid : Long) extends SynchronousRequest[Unit]
	private case class RequestOperation(op : Operation[_]) extends SynchronousRequest[Unit]
	private case class RequestSync(tx : Transaction) extends SynchronousRequest[Unit]

	private case object NotLockedException extends RuntimeException


	private [LowAkkaReplicaSystem] class LowReplicatedObject[Loc, T] (
    init : T, val addr : Loc, val replicaSystem : AkkaReplicaSystem {type Addr = Loc}
  )(
    protected implicit val ttt : TypeTag[T]
  ) extends AkkaReplicatedObject[Loc, T]
		with AkkaMultiversionReplicatedObject[Loc, T]
		with Lockable[T] {
		setObject(init)

		override final def consistencyLevel : ConsistencyLabel = Low

		private final val isRequest : DynamicVariable[Boolean] = new DynamicVariable(false)

//		@throws(classOf[TimeoutException])
//		def applySynchronous[T, R](op : Operation[T, R], input : T, timeout : FiniteDuration = FiniteDuration(30, "s")) : R  = {
//			//We implement 2-Phase-Commit for synchronous operations
//			val id = Random.nextLong()
//
//			val startTime = System.nanoTime()
//
//			while (true) {
//				//Phase 1: lock all replicas
//				if (lock.tryLock(id, timeout, op.objects)) { //Acquire local lock...
//					val readyResults = otherReplicas
//						.map(replica => replica.tryLock(id, op.objects, timeout))
//						.map(future => Await.result(future, timeout)) //... then try to acquire the lock of other replicas
//
//					if (readyResults.forall(identity)) { //If the lock has been acquired for all replicas...
//						//Phase 2: apply the Operation.
//						otherReplicas.foreach(replica => replica.commit(id, op, input))
//						val result = applyOp(op, input)
//						lock.unlock(id, op.objects)
//						return result
//					} else {
//						//Rollback Phase 1: Unlock all locks
//						otherReplicas.foreach(replica => replica.unlock(id, op.objects))
//						lock.unlock(id, op.objects)
//					}
//
//					Thread.sleep(Random.nextInt(1000))
//				}
//
//				//Timeout: abort trying 2PC
//				if ((System.nanoTime() - startTime) > timeout.toNanos) {
//					throw new TimeoutException
//				}
//			}
//
//			//This line should never be called.
//			throw new Exception()
//		}















		//Acquires a lock of all replicas of this object
		private def lockReplicas(tx : Transaction): Unit = {

			//Flag to indicate whether the lock on this object has suceeded
			var selfLocked = false
			//Buffer of replica refs that have been locked
			val lockedReplicas = mutable.Buffer.empty[ActorRef]

			//Set of all other replicas
			val otherReplicas = replicaSystem.getOtherReplicas

			while (true) {
				try {
					Predef.print(s"try lock = $addr, ${tx.id}... ")
					if (tryLock(tx.id))
						selfLocked = true
					else
						throw NotLockedException
					println("locked")

					for (replica <- otherReplicas) {
						Predef.print(s"try lock on remote = $addr, ${tx.id}...")
						val handler = replicaSystem.handlerFor(replica)
						val wasLocked = handler.request(addr, LockRequest(tx.id)).asInstanceOf[Boolean]
						handler.close()

						if (wasLocked)
							lockedReplicas += replica
						else
							throw NotLockedException

						println(s"locked")
					}

					tx.addLock(addr.asInstanceOf[String])
					return

				} catch {
					case NotLockedException =>
						println("!!! Could not grab locks. Retry... !!!")
						if (selfLocked) unlock(tx.id)
						for (replica <- lockedReplicas) {
							val handler = replicaSystem.handlerFor(replica)
							handler.request(addr, UnlockRequest(tx.id)).asInstanceOf[Boolean]
							handler.close()
						}
						selfLocked = false
						lockedReplicas.clear()

						Thread.sleep(Random.nextInt(1000))
				}
			}
		}




		override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
			if (isDistributed(tx) && !isRequest.value) {
				val invokeOp = InvokeOp(tx, methodName, args)
				println("starting top level invoke...")
				replicaSystem.foreachOtherReplica(handler => {
					handler.request(addr, RequestOperation(invokeOp))
				})
			}

			assert(unsafeCompareTxid(tx.id))

			super.internalInvoke(tx, methodName, args)
		}


		private def isDistributed(tx : Transaction) : Boolean = {
			tx.isToplevel || tx.getParent.exists(t => t.consistencyLevel != Low)
		}


		override def internalGetField[R](tx : Transaction, fldName : String) : R = {
			if (isDistributed(tx) && !isRequest.value) {
				println("starting top level get...")
				//Get operations also have to be send to other replicas to ensure correct unlocking.
				replicaSystem.foreachOtherReplica(handler => {
					handler.request(addr, RequestOperation(GetFieldOp(tx, fldName)))
				})
			}

			assert(unsafeCompareTxid(tx.id))

			super.internalGetField(tx, fldName)
		}

		override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
			if (isDistributed(tx) && !isRequest.value) {
				println("starting top level set...")
				replicaSystem.foreachOtherReplica(handler => {
					handler.request(addr, RequestOperation(SetFieldOp(tx, fldName, newVal)))
				})
			}

			assert(unsafeCompareTxid(tx.id))

			super.internalSetField(tx, fldName, newVal)
		}

		override def internalSync() : Unit = {
			//Sync is always the only member of a transaction. We have to unlock all locks that have been
			//acquired when the sync method was started.
			replicaSystem.foreachOtherReplica(handler => {
				handler.request(addr, RequestSync(replicaSystem.getCurrentTransaction))
			})

			assert(unsafeCompareTxid(replicaSystem.getCurrentTransaction.id))

			super.internalSync()
		}

		override def handleRequest[R](request : Request[R]) : R = request match {
			case LockRequest(txid) =>
				tryLock(txid).asInstanceOf[R] //Returns a boolean that states whether the lock has been acquired.

			case UnlockRequest(txid) =>
				unlock(txid).asInstanceOf[R]

			case RequestOperation(op) =>
				replicaSystem.setCurrentTransaction(op.tx)
				isRequest.withValue(true) {
					op match {
						case InvokeOp(tx, mthdName, args) =>
							println("executing requested invoke...")
							assert(isDistributed(tx))
							transactionStarted(tx)
							internalInvoke[Any](tx, mthdName, args)
							transactionFinished(tx) //Unlock all objects
						case SetFieldOp(tx, fldName, newVal) =>
							println(s"executing requested set...")
							assert(isDistributed(tx))
							internalSetField(tx, fldName, newVal)
							transactionFinished(tx) //Unlock all objects
						case GetFieldOp(tx, fldName) =>
							println(s"executing requested get...")
							assert(isDistributed(tx))
							//We do not need to execute the get, but only finish the transaction
							internalGetField(tx, fldName)
							transactionFinished(tx) //Unlock all objects
					}

					replicaSystem.clearTransaction().asInstanceOf[R]
				}

			case RequestSync(txid) =>
				replicaSystem.setCurrentTransaction(txid)
				transactionFinished(txid) //Unlock all objects
				replicaSystem.clearTransaction().asInstanceOf[R]


			case _ =>
				super.handleRequest(request)
		}

		override protected def transactionStarted(tx : Transaction) : Unit = {
			if (isDistributed(tx) && !isRequest.value) {
				lockReplicas(tx)
			} else {
				lock(tx.id)
				tx.addLock(addr.asInstanceOf[String])
			}
			super.transactionStarted(tx)
		}

		override protected def transactionFinished(tx : Transaction) : Unit = {
			super.transactionFinished(tx)
		}

		override def toString : String = s"@Low($addr, $getObject)"
	}


}




