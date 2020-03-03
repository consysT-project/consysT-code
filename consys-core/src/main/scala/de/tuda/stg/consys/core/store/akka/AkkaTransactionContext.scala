package de.tuda.stg.consys.core.store.akka

import akka.util.Timeout
import de.tuda.stg.consys.core.store.akka.AkkaStore.CreateObjectReplica
import de.tuda.stg.consys.core.store.{CommitableTransactionContext, TransactionContext}

import scala.concurrent.Await
import scala.reflect.ClassTag

/**
 * Created on 25.02.20.
 *
 * @author Mirko Köhler
 */
case class AkkaTransactionContext(override val store : AkkaStore) extends TransactionContext
	with CommitableTransactionContext {

	override type StoreType = AkkaStore

	
	override private[store] def replicateRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, level : StoreType#Level) : StoreType#RawType[T] = {
		require(!store.LocalReplica.contains(addr))

		val model = level.toModel(store)

		import akka.pattern.ask
		/*create the replicated object*/
		val replicatedObject = model.createMasterReplica[T](addr, obj, this)

		/*put the object in the local replica store*/
		store.LocalReplica.put(replicatedObject)

		/*notify other replicas for the new object.*/
		implicit val timeout : Timeout = store.timeout
		val futures = store.otherReplicas.map { actorRef =>
			actorRef ? CreateObjectReplica(addr, obj, level, store.replicaActor)
		}
		futures.foreach { future => Await.ready(future, store.timeout) }

		/*create a ref to that object*/
		replicatedObject
	}

	override private[store] def lookupRaw[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, level : StoreType#Level) : StoreType#RawType[T] =
		store.LocalReplica.get(addr).get.asInstanceOf[AkkaObject[T]]


	override private[store] def commit() : Unit = { }
}
