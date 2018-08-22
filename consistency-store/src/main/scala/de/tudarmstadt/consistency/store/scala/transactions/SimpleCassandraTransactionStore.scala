package de.tudarmstadt.consistency.store.scala.transactions

import scala.util.Random

/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
object SimpleCassandraTransactionStore extends CassandraTransactionStore[Int, String, String, String, String, String] {

	override val KEYSPACE_NAME : String = "k_transactions_simple"

	import SimpleTypeFactories._

	override protected def idOps : SimpleCassandraTransactionStore.IdOps[Int] =
		SimpleSeqIdOps
		//SimpleRanIdOps

	override protected def txStatusOps : SimpleCassandraTransactionStore.TxStatusOps[String] =
		SimpleTxStatusOps

	override protected def isolationLevelOps : SimpleCassandraTransactionStore.IsolationLevelOps[String] =
		SimpleIsolationLevelOps

	override protected def consistencyLevelOps : SimpleCassandraTransactionStore.ConsistencyLevelOps[String] =
		SimpleConsistencyLevelOps


	override val maxFunctionDef : String =
		s"""Integer maxid = max.get(0, Integer.class);
			 |
			 |  if (maxid == null || id > maxid) {
			 |			max.setInt(0, id);
			 |			max.setString(1, key);
			 |			max.setString(2, data);
			 |			max.setSet(3, deps, Integer.class);
			 |			max.set(4, txid, Integer.class);
			 |			max.setString(5, consistency);
			 |			return max;
			 |		} else {
			 |			return max;
			 |		}
		 """.stripMargin



	object SimpleTypeFactories {

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

		object SimpleTxStatusOps extends TxStatusOps[String] {
			override def pending : String = "pending"
			override def committed : String = "committed"
			override def aborted : String = "aborted"
		}

		object SimpleConsistencyLevelOps extends ConsistencyLevelOps[String] {
			override def sequential : String = "sequential"
		}

		object SimpleIsolationLevelOps extends IsolationLevelOps[String] {
			override def snapshotIsolation : String = "snapshot"
		}

	}

}
