package de.tuda.stg.consys.core.legacy.akka

import akka.actor.ActorRef
import akka.dispatch.ExecutionContexts
import de.tuda.stg.consys.core.legacy.ConsistencyLabel
import de.tuda.stg.consys.core.legacy.ConsistencyLabel.Cassandra
import de.tuda.stg.consys.core.legacy.akka.Requests.{AsynchronousRequest, Operation, Request}
import java.util.concurrent.{ConcurrentLinkedQueue, CountDownLatch}
import scala.collection.{JavaConverters, mutable}
import scala.language.postfixOps
import scala.reflect.runtime.universe._
import scala.util.{Failure, Success}


/**
	* Created on 27.02.19.
	*
	* @author Mirko Köhler
	*/

trait CassandraAkkaReplicaSystem extends AkkaReplicaSystem {


	override protected def createMasterReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T) : AkkaReplicatedObject[Addr, T] = l match {
		case Cassandra(_) => new CassandraAkkaReplicaSystem.CassandraReplicatedObject(obj, addr, this, l)
		case _ =>	super.createMasterReplica[T](l, addr, obj)
	}

	override protected def createFollowerReplica[T <: Obj : TypeTag](l : ConsistencyLevel, addr : Addr, obj : T, masterRef : ActorRef) : AkkaReplicatedObject[Addr, T] = l match {
		case Cassandra(_) => new CassandraAkkaReplicaSystem.CassandraReplicatedObject(obj, addr, this, l)
		case _ =>	super.createFollowerReplica[T](l, addr, obj, masterRef)
	}
}


object CassandraAkkaReplicaSystem {

	class CassandraReplicatedObject[Loc, T](
		init : T,
		val addr : Loc,
		val replicaSystem : AkkaReplicaSystem {type Addr = Loc},
		override val consistencyLevel : ConsistencyLabel
	)(
		protected implicit val ttt : TypeTag[T]
	) extends AkkaReplicatedObject[Loc, T] {
		setObject(init)

		private val objectTimestamp : Long = System.currentTimeMillis()
		private val fieldTimestamps : mutable.Map[String, Transaction] = mutable.Map.empty

		private def replicationFactor : Int = consistencyLevel match {
			case Cassandra(replicas) => replicas
			case _ => throw new IllegalArgumentException(s"unsupported cassandra consistency level $consistencyLevel")
		}


		override def internalInvoke[R](tx : Transaction, methodName: String, args: Seq[Seq[Any]]) : R = {
//			val result = super.internalInvoke(tx, methodName, args)
//
//			if (tx.isToplevel) {
//				val latch = new CountDownLatch(replicationFactor)
//				val results : ConcurrentLinkedQueue[R] = new ConcurrentLinkedQueue[R]()
//				results.offer(result)
//
//				replicaSystem.getOtherReplicas.foreach(actorRef => {
//					val handler = replicaSystem.handlerFor(actorRef)
//					handler
//						.request(addr, PropagateOperation(InvokeOp(tx, methodName, args)))
//						.onComplete {
//							case Success(value) =>
//								results.offer(value)
//								latch.countDown()
//								handler.close()
//							case Failure(exception) =>
//								latch.countDown()
//								handler.close()
//
//						} (ExecutionContexts.global())
//				})
//
//				latch.await()
//			}
//
//
//			result
			???
		}

		private def isNewer(tx : Transaction, fldName : String) : Boolean = fieldTimestamps.get(fldName) match {
			case None => true
			case Some(otherTx) => tx.timestamp > otherTx.timestamp
		}

		private def timestampOf(fldName : String) : Long = fieldTimestamps.get(fldName) match {
			case None => objectTimestamp
			case Some(tx) => tx.timestamp
		}


		override def internalGetField[R](tx : Transaction, fldName : String) : R = {
			val result = super.internalGetField[R](tx, fldName)

			if (tx.isToplevel) {
				val latch = new CountDownLatch(replicationFactor)
				val results : ConcurrentLinkedQueue[(Long, R)] = new ConcurrentLinkedQueue[(Long, R)]()

				replicaSystem.getOtherReplicas.foreach(actorRef => {
					val handler = replicaSystem.handlerFor(actorRef)
					handler
						.request(addr, PropagateGetField[R](tx, fldName))
						.onComplete {
							case Success(value) =>
								results.offer(value)
								latch.countDown()
								handler.close()
							case Failure(exception) =>
								latch.countDown()
								handler.close()

						} (ExecutionContexts.global())
				})

				latch.await()

				var current = (timestampOf(fldName), result)
				for (r <- JavaConverters.iterableAsScalaIterable(results)) {
					val (timestamp, value) = r
					if (timestamp > current._1) current = r
				}
				current._2

			} else {
				result
			}
		}


		override def internalSetField(tx : Transaction, fldName : String, newVal : Any) : Unit = {
			if (isNewer(tx, fldName)) return

			super.internalSetField(tx, fldName, newVal)
			fieldTimestamps(fldName) = tx

			if (tx.isToplevel) {
				val latch = new CountDownLatch(replicationFactor)

				replicaSystem.getOtherReplicas.foreach(actorRef => {
					val handler = replicaSystem.handlerFor(actorRef)
					handler
						.request(addr, PropagateSetField(tx, fldName, newVal))
						.onComplete {
							case Success(value) =>
								latch.countDown()
								handler.close()
							case Failure(exception) =>
								latch.countDown()
								handler.close()
						} (ExecutionContexts.global())
				})

				latch.await()
			}
		}

		override def internalSync() : Unit = {
			//super.internalSync()
			//	println("WARNING: sync on master")
		}

		override def handleRequest[R](request : Request[R]) : R = request match {
			case PropagateSetField(tx, fldName, newVal) =>
				if (isNewer(tx, fldName)) return ().asInstanceOf[R]

				super.internalSetField(tx, fldName, newVal)
				fieldTimestamps(fldName) = tx

				().asInstanceOf[R]

			case PropagateGetField(tx, fldName) =>
				val result = super.internalGetField[R](tx, fldName)
				(timestampOf(fldName), result).asInstanceOf[R]

			case _ =>
				super.handleRequest(request)
		}
	}


	case class PropagateOperation[R](op : Operation[R]) extends AsynchronousRequest[R]

	case class PropagateGetField[R](tx : Transaction, fldName : String) extends AsynchronousRequest[(Long, R)]
	case class PropagateSetField(tx : Transaction, fldName : String, value : Any) extends AsynchronousRequest[Unit]


}
