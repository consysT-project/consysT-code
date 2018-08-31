package de.tudarmstadt.consistency.store.scala.extra

import de.tudarmstadt.consistency.store.scala.extra.Util._
import de.tudarmstadt.consistency.store.scala.extra.Util.SimpleTypeFactories._
import de.tudarmstadt.consistency.store.scala.extra.internalstore.{ConnectionParams, SysnameCassandraStoreImpl}
import de.tudarmstadt.consistency.store.scala.extra.shim.{SysnameVersionedStore, SysnameVersionedStoreImpl}

import scala.util.Random

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
object Stores {

	def newSimpleStore(connectionParams : ConnectionParams, initialize : Boolean = false) : SysnameVersionedStore[Int, String, String, String, String] = {

		object SimpleSeqIdOps extends IdOps[Int] {
			var currentId = 0
			override def freshId() : Int = synchronized {
				currentId += 1
				currentId
			}
		}

		object SimpleRanIdOps extends IdOps[Int] {
			val random = new Random
			override def freshId() : Int = {
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

		val baseStore = new SysnameCassandraStoreImpl[Int, String, String, String, String, String](connectionParams)(keyOps, txStatusOps, isolationLevelOps, consistencyLevelOps)
		if (initialize) {
			baseStore.initializeKeyspace()
		}

		val versionedStore = new SysnameVersionedStoreImpl[Int, String, String, String, String](baseStore)(idOps, isolationLevelOps, consistencyLevelOps)

		versionedStore
	}

}
