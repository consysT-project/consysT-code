package de.tudarmstadt.consistency.store

import java.nio.ByteBuffer
import java.util.UUID
import java.util.concurrent.atomic.AtomicInteger

import com.datastax.driver.core.TypeCodec
import com.datastax.driver.core.utils.UUIDs
import de.tudarmstadt.consistency.store.cassandra.SysnameCassandraStoreImpl
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.{SysnameVersionedStore, SysnameVersionedStoreImpl}

import scala.util.Random
import scala.reflect.runtime.universe._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
object Stores {

	object Simple {

		private final type Id = Integer
		private final type Key = String
		private final type TxStatus = String
		private final type Isolation = String
		private final type Consistency = String

		private val keyspaceName = "k_sysname_simple"

		def createSeqIds : Ids[Id] = new Ids[Id] {
			var currentId : AtomicInteger = new AtomicInteger(0)

			override def freshId() : Integer =
				currentId.incrementAndGet()

		}

		private def createRanIds : Ids[Id] = new Ids[Id] {
			val random = new Random
			override def freshId() : Integer = {
				random.nextInt(1000)
			}
		}

		private def createKeys : Keys[Key] = new Keys[Key] {
			override def transactionKey : String = "$tx"
		}

		private def createTxStatuses : TxStatuses[TxStatus] = new TxStatuses[TxStatus] {
			override def pending : String = "pending"
			override def committed : String = "committed"
			override def aborted : String = "aborted"
		}

		private def createConsistencyLevels : ConsistencyLevels[Consistency] = new ConsistencyLevels[Consistency] {
			override def causal : String = "causal"
			override def weak : String = "weak"
		}

		private def createIsolationLevels : IsolationLevels[Isolation] = new IsolationLevels[Isolation] {
			override def snapshotIsolation : String = "ss"
			override def readUncommitted : String = "ru"
			override def readCommitted : String = "rc"
			override def none : String = "none"
		}



		/* TODO use Int instead of Integer. Problem: It gets casted to primitive int where primitive int is not allowed */
		def newStore[Data : TypeTag](connectionParams : ConnectionParams, idOps : Ids[Id] = createSeqIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Data]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			//TODO: we have to use the concrete types here instead of e.g. Id, because the type tags will not be resolved correctly
			//You get a TypeTag[Id] instead of a TypeTag[Integer] and then the type codec can not be resolved
			val baseStore = new SysnameCassandraStoreImpl[Integer, String, Data, String, String, String](
				connectionParams, keyspaceName
			)(
				keys, txStatuses, isolationLevels, consistencyLevels
			)()

			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, Data, String, String, String, Option[Data]](
				baseStore
			)(
				None, upd => Some(upd.data)
			)(
				idOps, keys, txStatuses, isolationLevels, consistencyLevels
			)

			versionedStore
		}

		def newTestStore[Data : TypeTag](connectionParams : ConnectionParams, idOps : Ids[Id] = createSeqIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			val baseStore = new SysnameCassandraStoreImpl[Integer, String, Data, String, String, String](
				connectionParams, keyspaceName
			)(
				keys, txStatuses, isolationLevels, consistencyLevels
			)()

			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, Data, String, String, String, Option[Update[Id, Key, Data]]](
				baseStore
			)(
				None, upd => Some(upd)
			)(
				idOps, keys, txStatuses, isolationLevels, consistencyLevels
			)

			versionedStore
		}
	}

	object Default {
		private type Id = UUID
		private type Key = String
		private type Data = ByteBuffer
		private type TxStatus = Int
		private type Isolation = Int
		private type Consistency = Int

		private val keyspaceName = "k_sysname"

		private def createIds : Ids[Id] = new Ids[Id] {
			override def freshId() : Id = UUIDs.timeBased()
		}

		private def createKeys : Keys[Key] = new Keys[Key] {
			override def transactionKey : String = "$tx"
		}

		private def createTxStatuses : TxStatuses[TxStatus] = new TxStatuses[TxStatus] {
			override def pending : Int = 0
			override def committed : Int = 1
			override def aborted : Int = -1
		}

		private def createConsistencyLevels : ConsistencyLevels[Consistency] = new ConsistencyLevels[Consistency] {
			override def causal : Int = 3
			override def weak : Int = 0
		}

		private def createIsolationLevels : IsolationLevels[Isolation] = new IsolationLevels[Isolation] {
			override def snapshotIsolation : Int = 4
			override def readUncommitted : Int = 1
			override def readCommitted : Int = 2
			override def none : Int = 0
		}


		def newStore(connectionParams : ConnectionParams, idOps : Ids[Id] = createIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Data]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			val baseStore = new SysnameCassandraStoreImpl[UUID, String, ByteBuffer, Int, Int, Int](
				connectionParams, keyspaceName
			)(
				keys, txStatuses, isolationLevels, consistencyLevels
			)(
				idTpe = TypeCodec.timeUUID()
			)

			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[UUID, String, ByteBuffer, Int, Int, Int, Option[ByteBuffer]](
				baseStore
			)(
				None, upd => Some(upd.data)
			)(
				idOps, keys, txStatuses, isolationLevels, consistencyLevels
			)

			versionedStore
		}

		def newTestStore(connectionParams : ConnectionParams, idOps : Ids[Id] = createIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			val baseStore = new SysnameCassandraStoreImpl[UUID, String, ByteBuffer, Int, Int, Int](
				connectionParams, keyspaceName
			)(
				keys, txStatuses, isolationLevels, consistencyLevels
			)(
				idTpe = TypeCodec.timeUUID()
			)

			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[UUID, String, ByteBuffer, Int, Int, Int, Option[Update[Id, Key, Data]]](
				baseStore
			)(
				None, upd => Some(upd)
			)(
				idOps, keys, txStatuses, isolationLevels, consistencyLevels
			)

			versionedStore
		}



	}



}
