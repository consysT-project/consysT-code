package de.tudarmstadt.consistency.store

import java.util.UUID

import de.tudarmstadt.consistency.store.cassandra.SysnameCassandraStoreImpl
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.{SysnameVersionedStore, SysnameVersionedStoreImpl}

import scala.util.Random

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
object Stores {

	object Simple {

		private type Id = Integer
		private type Key = String
		private type Data = String
		private type TxStatus = String
		private type Isolation = String
		private type Consistency = String

		private val keyspaceName = "k_sysname_simple"


		private def createSeqIds : Ids[Id] = new Ids[Id] {
			var currentId = 0
			override def freshId() : Integer = synchronized {
				currentId += 1
				currentId
			}
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
		def newStore(connectionParams : ConnectionParams, idOps : Ids[Id] = createSeqIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[String]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			val baseStore = new SysnameCassandraStoreImpl[Integer, String, String, String, String, String](connectionParams, keyspaceName)(keys, txStatuses, isolationLevels, consistencyLevels)()
			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, String, String, String, String, Option[Data]](baseStore)(idOps, keys, txStatuses, isolationLevels, consistencyLevels, None, upd => Some(upd.data))

			versionedStore
		}

		def newTestStore(connectionParams : ConnectionParams, idOps : Ids[Id] = createSeqIds, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]] = {
			val keys = createKeys
			val txStatuses = createTxStatuses
			val isolationLevels = createIsolationLevels
			val consistencyLevels = createConsistencyLevels

			val baseStore = new SysnameCassandraStoreImpl[Integer, String, String, String, String, String](
				connectionParams, keyspaceName
			)(
				keys, txStatuses, isolationLevels, consistencyLevels
			)()

			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, String, String, String, String, Option[Update[Id, Key, Data]]](
				baseStore
			)(
				idOps, keys, txStatuses, isolationLevels, consistencyLevels, None, upd => Some(upd)
			)

			versionedStore
		}
	}

	object Default {
		private type Id = UUID
		private type Key = String
		private type Data = AnyRef
		private type TxStatus = Int
		private type Isolation = Int
		private type Consistency = Int


	}



}
