package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import com.datastax.driver.core.ConsistencyLevel
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.storelayer.distribution.{OptimisticLockService, SessionService}

import scala.collection.{JavaConverters, mutable}

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraOptimisticLocksService[Id, Txid, Key] extends OptimisticLockService[Id, Txid, Key] {
	self : CassandraSessionService[Id, Txid, Key, _, _, _, _] =>
	import typeBinding._

	private val keyTableName : String = "t_keys"



	/* queries */
	def CREATE_LOCK_TABLE(): Unit = {
		session.execute(
			s"""CREATE TABLE $keyTableName
				 | (key ${TypeCodecs.Key.getCqlType.asFunctionParameterString},
				 | txid ${TypeCodecs.Txid.getCqlType.asFunctionParameterString},
				 | reads set<${TypeCodecs.Id.getCqlType.asFunctionParameterString}>,
				 | PRIMARY KEY(key))""".stripMargin
		)
	}


	/* operations of the lock service */

	/* returns None if the was available, else returns the reference to the lock before re-locking. */
	override def lockIfEmpty(key : Key, txid : Txid) : Option[LockDescription] = {
		import QueryBuilder._

		val lockResult = session.execute(update(keyTableName)
			.`with`(set("txid", txid))
			.where(QueryBuilder.eq("key", key))
			.onlyIf(QueryBuilder.eq("txid", null))
			.and(QueryBuilder.eq("reads", null))
			.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val row = lockResult.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (rowWasApplied(row)) {
			//If the lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Txid)
			val otherReads : Set[Txid] = JavaConverters.asScalaSet(row.getSet("reads", TypeCodecs.Txid.getJavaType)).toSet
			Some(LockDescription(key, Option(otherTxid).map(TxRef), otherReads.map(TxRef)))
		}
	}

	/* locks a key if it was locked by another tx before */
	override def lockIfOther(key : Key, txid : Txid, otherTxid : Option[Txid], otherReads : Set[Txid]) : Option[LockDescription] = {
		import QueryBuilder._


		val mutableOtherReads = mutable.Set.empty[Txid]
		mutableOtherReads ++= otherReads
		val javaOtherReads = JavaConverters.mutableSetAsJavaSet(mutableOtherReads)

		val lockResult = session.execute(update(keyTableName)
			.`with`(set("txid", txid))
			.and(set("reads", null)) //TODO: Remove all reads or retain txid as read?
			.where(QueryBuilder.eq("key", key))
			.onlyIf(QueryBuilder.eq("txid", otherTxid.getOrElse(null)))
			.and(QueryBuilder.eq("reads", javaOtherReads))
			.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val row = lockResult.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Txid)
			val otherReads : Set[Txid] = JavaConverters.asScalaSet(row.getSet("reads", TypeCodecs.Txid.getJavaType)).toSet
			Some(LockDescription(key, Option(otherTxid).map(TxRef), otherReads.map(TxRef)))
		}
	}

	override def addReadLock(key : Key, txid : Txid) : Option[Txid] = {
		import QueryBuilder._

		val updateReadKeys = session.execute(
			update(keyTableName)
				.`with`(add("reads", txid))
				.where(QueryBuilder.eq("key", key))
				.onlyIf(QueryBuilder.eq("txid", null))
		)

		val row = updateReadKeys.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Txid)
			Some(otherTxid)
		}
	}

	override def releaseLockAndAddRead(key : Key, txid : Txid, newReadTxid : Txid) : Option[Txid] = {
		import QueryBuilder._

		val releaseOtherTxidLock = session.execute(
			update(keyTableName)
				.`with`(set("txid", null))
				.and(add("reads", newReadTxid))
				.where(QueryBuilder.eq("key", key))
				.onlyIf(QueryBuilder.eq("txid", txid))
		)

		val row = releaseOtherTxidLock.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Txid)
			Some(otherTxid)
		}
	}

	override def releaseLock(key : Key, txid : Txid) : Option[Txid] = {
		import QueryBuilder._

		val releaseOtherTxidLock = session.execute(
			update(keyTableName)
				.`with`(set("txid", null))
				.where(QueryBuilder.eq("key", key))
				.onlyIf(QueryBuilder.eq("txid", txid))
		)

		val row = releaseOtherTxidLock.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Txid)
			Some(otherTxid)
		}
	}
}
