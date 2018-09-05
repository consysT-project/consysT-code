package de.tudarmstadt.consistency.store

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

		type Id = Integer
		type Key = String
		type Data = String
		type TxStatus = String
		type Isolation = String
		type Consistency = String


		def createSeqIdOps : IdOps[Id] = new IdOps[Id] {
			var currentId = 0
			override def freshId() : Integer = synchronized {
				currentId += 1
				currentId
			}
		}

		def createRanIdOps : IdOps[Id] = new IdOps[Id] {
			val random = new Random
			override def freshId() : Integer = {
				random.nextInt(1000)
			}
		}

		private def createKeyOps : KeyOps[Key] = new KeyOps[Key] {
			override def transactionKey : String = "$tx"
		}

		private def createTxStatusOps : TxStatusOps[TxStatus] = new TxStatusOps[TxStatus] {
			override def pending : String = "pending"
			override def committed : String = "committed"
			override def aborted : String = "aborted"
		}

		private def createConsistencyLevelOps : ConsistencyLevelOps[Consistency] = new ConsistencyLevelOps[Consistency] {
			override def sequential : String = "seq"
		}

		private def createIsolationLevelOps : IsolationLevelOps[Isolation] = new IsolationLevelOps[Isolation] {
			override def snapshotIsolation : String = "ss"
			override def readUncommitted : String = "ru"
			override def readCommitted : String = "rc"
			override def none : String = "none"
		}



		/* TODO use Int instead of Integer. Problem: It gets casted to primitive int where primitive int is not allowed */
		def newStore(connectionParams : ConnectionParams, idOps : IdOps[Id] = createSeqIdOps, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[String]] = {
			val keyOps = createKeyOps
			val txStatusOps = createTxStatusOps
			val isolationLevelOps = createIsolationLevelOps
			val consistencyLevelOps = createConsistencyLevelOps

			val baseStore = new SysnameCassandraStoreImpl[Integer, String, String, String, String, String](connectionParams)(keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps)
			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, String, String, String, String, Option[Data]](baseStore)(idOps, keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps, None, upd => Some(upd.data))

			versionedStore
		}

		def newTestStore(connectionParams : ConnectionParams, idOps : IdOps[Id] = createSeqIdOps, initialize : Boolean = false) : SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Option[Update[Id, Key, Data]]] = {
			val keyOps = createKeyOps
			val txStatusOps = createTxStatusOps
			val isolationLevelOps = createIsolationLevelOps
			val consistencyLevelOps = createConsistencyLevelOps

			val baseStore = new SysnameCassandraStoreImpl[Integer, String, String, String, String, String](connectionParams)(keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps)
			if (initialize) {
				baseStore.initializeKeyspace()
			}

			val versionedStore = new SysnameVersionedStoreImpl[Integer, String, String, String, String, String, Option[Update[Id, Key, Data]]](baseStore)(idOps, keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps, None, upd => Some(upd))

			versionedStore
		}


	}



}
