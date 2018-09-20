package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.{ConsistencyLevel, TupleValue}
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventRef.UpdateRef

import scala.collection.JavaConverters

/**
	* Created on 19.09.18.
	*
	* @author Mirko Köhler
	*/
object Writes {

	private def eventRefToCassandraTuple(store : SysnameCassandraStore[_, _, _, _, _, _])(ref : UpdateRef[_, _]) : TupleValue = {
		import store._

		val typ = cluster.getMetadata.newTupleType(idType.getCqlType, keyType.getCqlType)
		typ.newValue(ref.id.asInstanceOf[AnyRef], ref.key.asInstanceOf[AnyRef])
	}

	private def dependencySetToCassandraSet[Id, Key](store : SysnameCassandraStore[Id, Key, _, _, _, _])(set : Set[UpdateRef[Id, Key]]) : java.util.Set[TupleValue] = {
		JavaConverters.setAsJavaSet(set.map(eventRefToCassandraTuple(store)))
	}


	trait Write[TxStatus, Isolation] {
		def writeData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE)(txStatus : TxStatus, isolation : Isolation) : Unit
		def deleteData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE) : Unit
	}

	class WriteUpdate[Id, Key, Data, TxStatus, Isolation, Consistency](
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		val upd : Update[Id, Key, Data], val params : CassandraWriteParams[Consistency]
	) extends Write[TxStatus, Isolation] {
		import store._

		override def writeData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE)(txStatus : TxStatus, isolation : Isolation) : Unit = {
			val convertedTxid = upd.txid.map(ref => ref.id).getOrElse(null)
			val convertedDependencies : java.util.Set[TupleValue] = dependencySetToCassandraSet(store)(upd.readDependencies)

			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				update(keyspace.dataTable.name)
					.`with`(set("data", upd.data))
					.and(set("deps", convertedDependencies))
					.and(set("txid", convertedTxid))
					.and(set("txstatus", txStatus))
					.and(set("isolation", isolation))
					.and(set("consistency", params.consistency))
					.where(QueryBuilder.eq("key", upd.key))
					.and(QueryBuilder.eq("id", upd.id))
					.setConsistencyLevel(writeConsistency)
			)
		}

		override def deleteData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE) : Unit = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				delete().from(keyspace.dataTable.name)
  				.where(QueryBuilder.eq("key", upd.key))
  				.and(QueryBuilder.eq("id", upd.id))
			)
		}
	}

	class WriteTx[Id, Key, Data, TxStatus, Isolation, Consistency](
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		val tx : Tx[Id, Key, Data], val params : CassandraWriteParams[Consistency]
	) extends Write[TxStatus, Isolation] {
		import store._

		override def writeData(session : CassandraSession, writeConsistency : ConsistencyLevel)(txStatus : TxStatus, isolation : Isolation) : Unit = {
			val convertedDependencies : java.util.Set[TupleValue] = dependencySetToCassandraSet(store)(tx.readDependencies)

			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				update(keyspace.dataTable.name)
					.`with`(set("data", null))
					.and(set("deps", convertedDependencies))
					.and(set("txid", tx.id))
					.and(set("txstatus", txStatus))
					.and(set("isolation", isolation))
					.and(set("consistency", params.consistency))
					.where(QueryBuilder.eq("key", Keys.transactionKey))
					.and(QueryBuilder.eq("id", tx.id))
					.setConsistencyLevel(writeConsistency)
			)
		}

		override def deleteData(session: CassandraSession, writeConsistency: ConsistencyLevel = ConsistencyLevel.ONE) : Unit = {
			import com.datastax.driver.core.querybuilder.QueryBuilder._
			session.execute(
				delete().from(keyspace.dataTable.name)
					.where(QueryBuilder.eq("key", Keys.transactionKey))
					.and(QueryBuilder.eq("id", tx.id))
			)
		}
	}

}
