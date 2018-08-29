package de.tudarmstadt.consistency.store.scala.transactions

import scala.reflect.runtime.universe._
import scala.util.Random

/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
class SimpleCassandraTransactionStore(protected val connectionParams : ConnectionParams)
	extends SysnameStore[Int, String, String, String, String, String]
	with SysnameSnapshotIsolatedTransactionStore[Int, String, String, String, String, String]
	with SysnameReadCommittedTransactionStore[Int, String, String, String, String, String]
{


	import SimpleTypeFactories._

	override def idOps : IdOps[Int] =
		SimpleSeqIdOps
		//SimpleRanIdOps

	override def txStatusOps : TxStatusOps[String] =
		SimpleTxStatusOps

	override def isolationLevelOps : IsolationLevelOps[String] =
		SimpleIsolationLevelOps

	override def consistencyLevelOps : ConsistencyLevelOps[String] =
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
			override def sequential : String = "seq"
		}

		object SimpleIsolationLevelOps extends IsolationLevelOps[String] {
			override def snapshotIsolation : String = "ss"
			override def readUncommitted : String = "ru"
			override def readCommitted : String = "rc"
		}

	}

}
