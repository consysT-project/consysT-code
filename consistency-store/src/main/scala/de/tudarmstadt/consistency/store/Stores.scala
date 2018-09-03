package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.cassandra.SysnameCassandraStoreImpl
import de.tudarmstadt.consistency.store.shim.{SysnameVersionedStore, SysnameVersionedStoreImpl}

import scala.util.Random

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
object Stores {

	/* TODO use Int instead of Integer. Problem: It gets casted to primitive int where primitive int is not allowed */
	def newSimpleStore(connectionParams : ConnectionParams, initialize : Boolean = false) : SysnameVersionedStore[Integer, String, String, String, String, String] = {

		object SimpleSeqIdOps extends IdOps[Integer] {
			var currentId = 0
			override def freshId() : Integer = synchronized {
				currentId += 1
				currentId
			}
		}

		object SimpleRanIdOps extends IdOps[Integer] {
			val random = new Random
			override def freshId() : Integer = {
				random.nextInt(1000)
			}
		}

		object SimpleKeyOps extends KeyOps[String] {
			override def transactionKey : String = "$tx"
		}

		object SimpleTxStatusOps extends TxStatusOps[String] {
			override def pending : String = "pending"
			override def committed : String = "committed"
			override def aborted : String = "aborted"
		}

		object SimpleConsistencyLevelOps extends ConsistencyLevelOps[String] {
			override def sequential : String = "seq"
		}

		object SimpleIsolationLevelOps extends IsolationLevelOps[String] {
			override def snapshotIsolation : String = "ss"
			override def readUncommitted : String = "ru"
			override def readCommitted : String = "rc"
			override def none : String = "none"
		}


		val idOps = SimpleSeqIdOps
		val keyOps = SimpleKeyOps
		val txStatusOps = SimpleTxStatusOps
		val isolationLevelOps = SimpleIsolationLevelOps
		val consistencyLevelOps = SimpleConsistencyLevelOps

		val baseStore = new SysnameCassandraStoreImpl[Integer, String, String, String, String, String](connectionParams)(keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps)
		if (initialize) {
			baseStore.initializeKeyspace()
		}

		val versionedStore = new SysnameVersionedStoreImpl[Integer, String, String, String, String, String](baseStore)(idOps, keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps)

		versionedStore
	}

}
