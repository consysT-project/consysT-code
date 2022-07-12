package de.tuda.stg.consys.core.store.akka.levels

import akka.actor.ActorRef
import de.tuda.stg.consys.core.store.ConsistencyProtocol
import de.tuda.stg.consys.core.store.akka.AkkaStore

import scala.reflect.ClassTag

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait AkkaConsistencyProtocol extends ConsistencyProtocol {
	override type StoreType = AkkaStore
	override type Level = AkkaConsistencyLevel

	def createMasterReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#HandlerType[T]
	def createFollowerReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, masterRef : ActorRef, txContext : StoreType#TxContext) : StoreType#HandlerType[T]

}
