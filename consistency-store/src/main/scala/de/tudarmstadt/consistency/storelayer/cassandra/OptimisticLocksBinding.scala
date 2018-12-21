package de.tudarmstadt.consistency.storelayer.cassandra

import com.datastax.driver.core.ConsistencyLevel
import com.datastax.driver.core.querybuilder.QueryBuilder

import scala.collection.{JavaConverters, mutable}

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait OptimisticLocksBinding[Id, Key] {
	self : SessionBinding[Id, Key, _, _, _, _] =>
	import typeBinding._

	private val keyTableName : String = "t_keys"

	/* class definitions */
	case class LockDescription(key : Key, txid : Option[TxRef], reads : Set[TxRef])

	/* queries */
	def CREATE_LOCK_TABLE(): Unit = {
		session.execute(
			s"""CREATE TABLE $keyTableName
				 | (key ${TypeCodecs.Key.getCqlType.asFunctionParameterString},
				 | txid ${TypeCodecs.Id.getCqlType.asFunctionParameterString},
				 | reads set<${TypeCodecs.Id.getCqlType.asFunctionParameterString}>,
				 | PRIMARY KEY(key))""".stripMargin
		)
	}


	/* operations of the lock service */

	/* returns None if the key was not used by another transaction, else returns the txid. */
	def lockIfEmpty(key : Key, txid : Id) : Option[LockDescription] = {
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

		if (CassandraUtils.rowWasApplied(row)) {
			//If the lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Id)
			val otherReads : Set[Id] = JavaConverters.asScalaSet(row.getSet("reads", TypeCodecs.Id.getJavaType)).toSet
			Some(LockDescription(key, Option(otherTxid).map(TxRef), otherReads.map(TxRef)))
		}
	}

	/* locks a key if it was locked by another tx before */
	def lockIfOther(key : Key, txid : Id, otherTxid : Option[Id], otherReads : Set[Id]) : Option[LockDescription] = {
		import QueryBuilder._


		val mutableOtherReads = mutable.Set.empty[Id]
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

		if (CassandraUtils.rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Id)
			val otherReads : Set[Id] = JavaConverters.asScalaSet(row.getSet("reads", TypeCodecs.Id.getJavaType)).toSet
			Some(LockDescription(key, Option(otherTxid).map(TxRef), otherReads.map(TxRef)))
		}
	}

	def addReadLock(key : Key, txid : Id) : Option[Id] = {
		import QueryBuilder._

		val updateReadKeys = session.execute(
			update(keyTableName)
				.`with`(add("reads", txid))
				.where(QueryBuilder.eq("key", key))
				.onlyIf(QueryBuilder.eq("txid", null))
		)

		val row = updateReadKeys.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (CassandraUtils.rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Id)
			Some(otherTxid)
		}
	}

	def releaseLockAndAddRead(key : Key, txid : Id, newReadTxid : Id) : Option[Id] = {
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

		if (CassandraUtils.rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Id)
			Some(otherTxid)
		}
	}

	def releaseLock(key : Key, txid : Id) : Option[Id] = {
		import QueryBuilder._

		val releaseOtherTxidLock = session.execute(
			update(keyTableName)
				.`with`(set("txid", null))
				.where(QueryBuilder.eq("key", key))
				.onlyIf(QueryBuilder.eq("txid", txid))
		)

		val row = releaseOtherTxidLock.one()
		assert(row != null, s"table $keyTableName did not return a result for update query")

		if (CassandraUtils.rowWasApplied(row)) {
			//If lock was set
			None
		} else {
			//If the lock was not set
			val otherTxid = row.get("txid", TypeCodecs.Id)
			Some(otherTxid)
		}
	}
}
