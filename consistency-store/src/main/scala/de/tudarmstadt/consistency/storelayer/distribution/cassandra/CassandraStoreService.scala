package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ConsistencyLevel, ResultSet, Row, TupleValue}
import de.tudarmstadt.consistency.storelayer.distribution.StoreService

import scala.collection.JavaConverters

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraStoreService[Id, Key, Data, TxStatus, Isolation, Consistency] extends StoreService[Id, Key, Data, TxStatus, Isolation, Consistency] {
	self : CassandraSessionService[Id, Key, Data, TxStatus, Isolation, Consistency] =>
	import typeBinding._

	private val opTableName : String = "t_data"
	private val txTableName : String = "t_tx"

	/*TODO: generalize cassandra consistency level*/
	private val cassandraConsistency : ConsistencyLevel = ConsistencyLevel.QUORUM



	/* class definitions */

	/* rows that have been read from the store */
	class CassandraOpRow(private val row : Row) extends OpRow {
		Seq("id", "key", "data", "txid", "deps", "txstatus", "isolation", "consistency").foreach(name =>
			assert(row.getColumnDefinitions.contains(name), s"expected update row to contain field $name")
		)

		lazy val id : Id = row.get("id", TypeCodecs.Id)
		lazy val key : Key = row.get("key", TypeCodecs.Key)
		lazy val data : Data = row.get("data", TypeCodecs.Data)
		lazy val txid : Option[TxRef] =	Option(row.get("txid", TypeCodecs.Id)).map(id => TxRef(id))


		lazy val deps : Set[OpRef] = {
			val it : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", classOf[TupleValue])).toSet
			it.map(tv => OpRef(tv.get(0, TypeCodecs.Id), tv.get(1, TypeCodecs.Key)))
		}
		lazy val txStatus : TxStatus = row.get("txstatus", TypeCodecs.TxStatus)
		lazy val isolation : Isolation = row.get("isolation", TypeCodecs.Isolation)
		lazy val consistency : Consistency = row.get("consistency", TypeCodecs.Consistency)
	}


	class CassandraTxRow(private val row : Row) extends TxRow {
		//Check whether all fields are available
		Seq("id", "deps", "txstatus", "isolation", "consistency").foreach(name =>
			assert(row.getColumnDefinitions.contains(name), s"expected tx row to contain field $name")
		)

		lazy val id : Id = row.get("id", TypeCodecs.Id)

		lazy val deps : Set[OpRef] = {
			val it : Set[TupleValue] = JavaConverters.asScalaSet(row.getSet("deps", classOf[TupleValue])).toSet
			it.map(tv => OpRef(tv.get(0, TypeCodecs.Id), tv.get(1, TypeCodecs.Key)))
		}

		lazy val txStatus : TxStatus = row.get("txstatus", TypeCodecs.TxStatus)
		lazy val isolation : Isolation = row.get("isolation", TypeCodecs.Isolation)
		lazy val consistency : Consistency = row.get("consistency", TypeCodecs.Consistency)
	}




	/* cql queries */

	def CREATE_DATA_TABLE() : Unit = {
		session.execute(
			s"""CREATE TABLE $opTableName
				 | (id ${TypeCodecs.Id.getCqlType.asFunctionParameterString()},
				 | key ${TypeCodecs.Key.getCqlType.asFunctionParameterString},
				 | data ${TypeCodecs.Data.getCqlType.asFunctionParameterString},
				 | deps set<frozen<tuple<${TypeCodecs.Id.getCqlType.asFunctionParameterString}, ${TypeCodecs.Key.getCqlType.asFunctionParameterString}>>>,
				 | txid ${TypeCodecs.Id.getCqlType.asFunctionParameterString},
				 | txstatus ${TypeCodecs.TxStatus.getCqlType.asFunctionParameterString},
				 | consistency ${TypeCodecs.Consistency.getCqlType.asFunctionParameterString},
				 | isolation ${TypeCodecs.Isolation.getCqlType.asFunctionParameterString},
				 | PRIMARY KEY (key, id))""".stripMargin
		)

		session.execute(
			s"""CREATE TABLE $txTableName
				 | (id ${TypeCodecs.Id.getCqlType.asFunctionParameterString()},
				 | deps set<frozen<tuple<${TypeCodecs.Id.getCqlType.asFunctionParameterString}, ${TypeCodecs.Key.getCqlType.asFunctionParameterString}>>>,
				 | txstatus ${TypeCodecs.TxStatus.getCqlType.asFunctionParameterString},
				 | consistency ${TypeCodecs.Consistency.getCqlType.asFunctionParameterString},
				 | isolation ${TypeCodecs.Isolation.getCqlType.asFunctionParameterString},
				 | PRIMARY KEY (id))""".stripMargin
		)
	}



	override def writeData(id : Id, key : Key, data : Data, txid : Option[TxRef], dependencies : Set[OpRef], txStatus : TxStatus, isolation : Isolation, consistency : Consistency) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val convertedTxid = txid.map(_.id).getOrElse(null)

		val convertedDependencies : java.util.Set[TupleValue] = JavaConverters.setAsJavaSet(
			dependencies.map(t => tupleToCassandraTuple(t.toTuple)(this))
		)

		session.execute(
			update(opTableName)
				.`with`(set("data", data))
				.and(set("deps", convertedDependencies))
				.and(set("txid", convertedTxid))
				.and(set("txstatus", txStatus))
				.and(set("isolation", isolation))
				.and(set("consistency", consistency))
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
				.setConsistencyLevel(cassandraConsistency)
		)
	}


	override def updateTxStatusInData(id : Id, key : Key, txStatus : TxStatus) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		session.execute(
			update(opTableName)
				.`with`(set("txstatus", txStatus))
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
		)
	}

	override def deleteData(id : Id, key : Key) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._
		session.execute(
			delete().from(opTableName)
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
		)
	}



	override def readData(id : Id, key : Key) : Option[OpRow] = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Retrieve the history of a key.
		val keyResult = session.execute(
			select.all.from(opTableName)
				.where(QueryBuilder.eq("key", key))
				.and(QueryBuilder.eq("id", id))
		)

		val row = keyResult.one()
		if (row == null) {
			return None
		}
		Some(new CassandraOpRow(row))
	}

	override def readAllData(key : Key) : Iterable[OpRow] = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Retrieve the history of a key.
		val keyResult = session.execute(
			select.all.from(opTableName)
				.where(QueryBuilder.eq("key", key))
		)

		val it : Iterator[OpRow] = new Iterator[OpRow] {
			private val result : ResultSet = keyResult
			private var currentPosition : Row = result.one

			override def hasNext : Boolean = currentPosition != null
			override def next() : OpRow = {
				val next = currentPosition
				currentPosition = result.one()
				new CassandraOpRow(next)
			}
		}

		return it.toIterable
	}



	override def writeTx(id : Id, dependencies : Set[OpRef], txStatus : TxStatus, isolation : Isolation, consistency : Consistency) : Unit = {
		val convertedDependencies : java.util.Set[TupleValue] = JavaConverters.setAsJavaSet(
			dependencies.map(t => tupleToCassandraTuple(t.toTuple)(this))
		)

		import com.datastax.driver.core.querybuilder.QueryBuilder._
		session.execute(
			update(txTableName)
				.`with`(set("deps", convertedDependencies))
				.and(set("txstatus", txStatus))
				.and(set("isolation", isolation))
				.and(set("consistency", consistency))
				.where(QueryBuilder.eq("id", id))
				.setConsistencyLevel(cassandraConsistency)
		)
	}

	override def deleteTx(id : Id) : Unit = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._
		session.execute(
			delete().from(txTableName)
				.where(QueryBuilder.eq("id", id))
		)
	}

	override def readTx(id : Id) : Option[TxRow] = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Retrieve the history of a key.
		val keyResult = session.execute(
			select.all.from(txTableName)
				.where(QueryBuilder.eq("id", id))
		)

		val row = keyResult.one()
		if (row == null) {
			return None
		}
		Some(new CassandraTxRow(row))
	}



}
