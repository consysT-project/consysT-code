package de.tudarmstadt.consistency.store.scala.extra.internalstore

import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.querybuilder.QueryBuilder.select
import com.datastax.driver.core.{ConsistencyLevel, Session, WriteType}
import de.tudarmstadt.consistency.store.scala.extra.Util.{CommitStatus, ReadStatus}

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._

/*
TODO: The current implementation of read committed isolation has still some problems.

* it allows dirty reads
* it allows dirty writes

 */
/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object ReadCommittedTransactions {


	def commit[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return]
	(
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txid : Id,
		updates : Set[CassandraUpdate[Id, Key, Data]],
		result : Return
	): CommitStatus[Id, Return]	= {

		import CommitStatus._

		val updatedIds : Set[Id] = updates.map(upd => upd.id)

		try {

			updates.foreach(upd => {
				val CassandraUpdate(id, key, data, deps) = upd

				store.writeData(session, ConsistencyLevel.ONE)(
					id, key, data, deps, txid, store.txStatusOps.committed, store.consistencyLevelOps.sequential, store.isolationLevelOps.readCommitted
				)
			})

			store.writeNullData(session, ConsistencyLevel.ONE)(
				txid, store.keyOps.transactionKey, updatedIds, txid, store.txStatusOps.pending, store.consistencyLevelOps.sequential, store.isolationLevelOps.readCommitted
			)


		} catch {
			//TODO: Do proper error handling here
			case e : Exception => return Error(txid, e)
		}

		return Success(txid, updatedIds, result)
	}


	def read[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
		session : Session,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		key : Key
	): ReadStatus[Id, Key, Data] = {

		import ReadStatus._


		//Retrieve the maximum id for a given key
		val maxResult = session.execute(select().max("id")
			.from(store.keyspace.dataTable.name)
			.where(QueryBuilder.eq("key", key))
		)

		val maxRow = maxResult.one()

		if (maxRow == null) {
			//			assert(false, "did not retrieve anything from database")
			return NotFound(key, s"no entry for $key in database")
		}


		val readId = maxRow.get("system.max(id)", runtimeClassOf[Id])

		if (readId == null) {
			//			assert(false, "no rows left for key " + key)
			return NotFound(key, s"no entry for $key in database")
		}

		//Retrieve the row with the maximum id
		val readResult = session.execute(select().all()
			.from(store.keyspace.dataTable.name)
			.where(QueryBuilder.eq("id", readId))
			.and(QueryBuilder.eq("key", key))
		)

		/*TODO: Another possibility would be to use the user defined maxRow which returns the complete row (in the aggregation) instead of just one column.

		I have to make weigh the differences between these to possibilities.

		select maxRow(id, key, data, deps, txid, consistency) from t_data where key = 'x';

		 */

		val readRow = readResult.one()

		if (readRow == null) {
			//			assert(false, "did not retrieve anything from database")
			return NotFound(key, s"no entry for $key in database anymore (it may have been removed concurrently)")
			//TODO: Retry here???
		}

		val id = readRow.get("id", runtimeClassOf[Id])
		val data = readRow.get("data", runtimeClassOf[Data])
		val deps = JavaConverters.asScalaSet(readRow.getSet("deps", runtimeClassOf[Id])).toSet

		return Success(key, id, data, deps)
	}

}
