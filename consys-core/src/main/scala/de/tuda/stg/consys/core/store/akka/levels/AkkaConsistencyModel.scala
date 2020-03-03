package de.tuda.stg.consys.core.store.akka.levels

import akka.actor.ActorRef
import de.tuda.stg.consys.core.store.StoreConsistencyModel
import de.tuda.stg.consys.core.store.akka.AkkaStore

import scala.reflect.ClassTag

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait AkkaConsistencyModel extends StoreConsistencyModel {
	override type StoreType = AkkaStore
	override type Level = AkkaConsistencyLevel

	def createMasterReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#RawType[T]
	def createFollowerReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, masterRef : ActorRef, txContext : StoreType#TxContext) : StoreType#RawType[T]

}
