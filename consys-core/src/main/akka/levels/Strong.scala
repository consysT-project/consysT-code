package de.tuda.stg.consys.core.store.akka.levels

import akka.actor.ActorRef
import de.tuda.stg.consys.core.store.akka.Requests._
import de.tuda.stg.consys.core.store.akka.{AkkaObject, AkkaStore, AkkaStores}

import scala.collection.mutable
import scala.reflect.ClassTag

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
case object Strong extends AkkaConsistencyLevel {
	override def toProtocol(store : StoreType) : Protocol = new StrongProtocol(store)

	private class StrongProtocol(val store : AkkaStore) extends AkkaConsistencyProtocol {
		override def toLevel : Level = Weak

		def createMasterReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, txContext : StoreType#TxContext) : StoreType#HandlerType[T] = {
			new StrongMasterAkkaObject[T](addr, obj, store, txContext)
		}

		def createFollowerReplica[T <: StoreType#ObjType : ClassTag](addr : StoreType#Addr, obj : T, masterRef : ActorRef, txContext : StoreType#TxContext) : StoreType#HandlerType[T] = {
			new StrongMasterAkkaObject[T](addr, obj, store, txContext)
		}
	}


	private class StrongMasterAkkaObject[T <: StoreType#ObjType : ClassTag](override val addr : String, private var internalState : T, store : StoreType, txContext : StoreType#TxContext) extends AkkaObject[T] {
		override def consistencyLevel : AkkaStore#Level = Strong

		override def state : T = internalState

		override def invoke[R](methodName: String, args: Seq[Seq[Any]]) : R = {
			val lock = store.lockFor(addr)
			lock.acquire()
			val result = super.invoke(methodName, args)
			txContext
			lock.release()
			result
		}

		override def getField[R](fldName : String) : R = {
			val lock = store.lockFor(addr)
			lock.acquire()
			val result = super.getField(fldName)
			lock.release()
			result
		}

		override def setField[R](fldName : String, newVal : R) : Unit = {
			val lock = store.lockFor(addr)
			lock.acquire()
			super.setField(fldName, newVal)
			lock.release()
		}

		override def toString : String = s"StrongMaster($addr, $state)"

		override def sync() : Unit = ???
	}

	private class StrongFollowerAkkaObject[T <: StoreType#ObjType : ClassTag](override val addr : String, private var internalState : T, store : StoreType, masterRef : ActorRef, txContext : StoreType#TxContext) extends AkkaObject[T] {
		throw new UnsupportedOperationException("Do not use follower objects for strong.")

		override def consistencyLevel : AkkaStore#Level = Strong

		override def state : T = internalState

		override def invoke[R](methodName: String, args: Seq[Seq[Any]]) : R = {
			super.invoke(methodName, args)
		}

		override def getField[R](fldName : String) : R = {
			super.getField(fldName)
		}

		override def setField[R](fldName : String, newVal : R) : Unit = {
			super.setField(fldName, newVal)
		}


		def sync() : Unit = {
			???
		}

		override def toString : String = s"StrongFollower($addr, $state)"
	}
}




