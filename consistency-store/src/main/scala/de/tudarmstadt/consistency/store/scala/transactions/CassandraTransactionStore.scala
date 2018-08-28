package de.tudarmstadt.consistency.store.scala.transactions

import java.util.UUID

import com.datastax.driver.core._
import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.utils.Log

import scala.reflect.runtime.universe._

import scala.collection.JavaConverters

/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
abstract class CassandraTransactionStore[Id : TypeTag,	Key : TypeTag, Data : TypeTag,	TxStatus : TypeTag, ConsistencyLevel : TypeTag, IsolationLevel : TypeTag] {

	protected val KEYSPACE_NAME : String

	protected val TABLE_TX : String = "t_tx"
	protected val TABLE_KEYS : String = "t_keys"
	protected val TABLE_DATA : String = "t_data"

	/**
		* Define a function body (as Java source) that is used to compute the more up-to-date
		* row of two given rows.
		* The parameters that are available are id, key, data, dependencies (as a set), txid, and consistency.
		* The types are as defined by the type factories.
		*/
	protected val maxFunctionDef : String

	protected trait IdOps[T] {
		def freshId() : T
	}

	protected trait TxStatusOps[T] {
		def pending : T
		def committed : T
		def aborted : T
	}

	protected trait IsolationLevelOps[T] {
		def snapshotIsolation : T
	}

	protected trait ConsistencyLevelOps[T] {
		def sequential : T
	}

	protected def idOps : IdOps[Id]
	protected def txStatusOps : TxStatusOps[TxStatus]
	protected def isolationLevelOps : IsolationLevelOps[IsolationLevel]
	protected def consistencyLevelOps : ConsistencyLevelOps[ConsistencyLevel]



	protected def cassandraTypeOf[T : TypeTag] : String = implicitly[TypeTag[T]] match {

			//TODO: Is it possible to use CodecRegistry and/or DataType for that task?

		case t if t == typeTag[Boolean] => "boolean"

		case t if t == typeTag[Int] => "int"

		case t if t == typeTag[Float] => "float"
		case t if t == typeTag[Double] => "double"
		case t if t == typeTag[BigDecimal] => "decimal"

		case t if t == typeTag[String] => "text"

		case t if t == typeTag[UUID] => "uuid" //TODO Differentiate between UUID and TimeUUID

		case t => throw new IllegalArgumentException(s"can not infer a cassandra type from type tag $t")
	}



	private def idType = cassandraTypeOf[Id]
	private def keyType = cassandraTypeOf[Key]
	private def dataType = cassandraTypeOf[Data]
	private def txStatusType = cassandraTypeOf[TxStatus]
	private def consistencyLevelType = cassandraTypeOf[ConsistencyLevel]
	private def isolationLevelType = cassandraTypeOf[IsolationLevel]

	private var cluster : Cluster = null

	def initialize(): Unit = {
		connectCluster()
		createTables()
	}

	def connectCluster(address : String = "127.0.0.1", port : Int = 9042): Unit = {
		cluster = Cluster.builder.addContactPoint(address).withPort(port).build
	}

	def createTables(): Unit = {
		//Initialize a new keyspace
		val session: Session = cluster.newSession


		//Strategy NetworkTopologyStrategy does not support a replication factor.
		val replicationStrategy = "SimpleStrategy"

		//Initialize the keyspace
		session.execute(s"DROP KEYSPACE IF EXISTS $KEYSPACE_NAME;")
		session.execute(
			s"""CREATE KEYSPACE $KEYSPACE_NAME
				 | WITH replication = {'class': 'SimpleStrategy', 'replication_factor': 3 };""".stripMargin
		)

		//Use the keypsace as default keyspace
		session.execute(s"USE $KEYSPACE_NAME;")

		//Initialize tables
		session.execute(
			s"""CREATE TABLE $TABLE_TX
				 | (txid $idType,
				 | status $txStatusType,
				 | isolation $isolationLevelType,
				 | PRIMARY KEY(txid));""".stripMargin)
		session.execute(
			s"""CREATE TABLE $TABLE_KEYS
				 | (key $keyType,
				 | txid $idType,
				 | PRIMARY KEY(key));""".stripMargin)
		session.execute(
			s"""CREATE TABLE $TABLE_DATA
				 | (id $idType,
				 | key $keyType,
				 | data $dataType,
				 | deps set<$idType>,
				 | txid $idType,
				 | consistency $consistencyLevelType,
				 | PRIMARY KEY (key, id));""".stripMargin)

		//Create aggregate function for reading most up-to-date row

		//tuple of (id, key, data, deps, txid, consistency)
		val returnType = s"tuple<$idType, $keyType, $dataType, set<$idType>, $idType, $consistencyLevelType>"

		session.execute(
			s"""CREATE OR REPLACE FUNCTION biggerRow(
				 |  max $returnType,
				 |  id $idType, key $keyType, data $dataType, deps set<$idType>, txid $idType, consistency $consistencyLevelType)
				 |		CALLED ON NULL INPUT
				 |		RETURNS $returnType
				 |		LANGUAGE java
				 |		AS '$maxFunctionDef';
			 """.stripMargin)


		session.execute(
			s"""CREATE OR REPLACE AGGREGATE maxRow($idType, $keyType, $dataType, set<$idType>, $idType, $consistencyLevelType)
				 |SFUNC biggerRow
				 |STYPE $returnType
				 |INITCOND (null, null, null, null, null, null);
				 |
			 """.stripMargin
		)



		/*





		 */


		Thread.sleep(5000)
		session.close()
	}


	def close(): Unit = {
		cluster.close()
	}

	def newSession : Session = {
		cluster.connect(KEYSPACE_NAME)
	}


	private def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")


	case class Write(key : Key, data : Data, dependencies : Set[Id])


	trait CommitStatus
	object CommitStatus {
		case class Success(txid : Id, writtenIds : List[Id]) extends CommitStatus
		case class Error(txid : Id, error : Throwable) extends CommitStatus
		case class Abort(txid : Id, description : String) extends CommitStatus
	}


	def commitTransaction(session : Session, writes : List[Write]): CommitStatus = {
		import CommitStatus._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//2. Retrieve a fresh transaction id
		val txid : Id = idOps.freshId()

		try { //Catch exceptions when running CAS queries

			//3. Add a new entry into the transaction table (lightweight transaction)
			val txInsertResult = session.execute(
				insertInto(TABLE_TX)
					.values(
						Array[String]("txid", "status", "isolation"),
						Array[AnyRef](txid.asInstanceOf[AnyRef], txStatusOps.pending.asInstanceOf[AnyRef], isolationLevelOps.snapshotIsolation.asInstanceOf[AnyRef])
					)
					.ifNotExists()
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)

			//3.1. If the transaction id was already in use abort!
			if (!txInsertResult.wasApplied()) {
				//	assert(assertion = false, "transaction not added to the tx table")
				return Abort(txid, s"the chosen, fresh txid already exists. txid = $txid")
			}

			//4. Update all keys for writes in the key table
			writes.foreach(write => {
				val updateKeyResult = session.execute(
					update(TABLE_KEYS)
						.`with`(set("txid", txid))
						.where(QueryBuilder.eq("key", write.key))
						.onlyIf(QueryBuilder.eq("txid", null))
						.setConsistencyLevel(ConsistencyLevel.ALL)
				)

				//4.1. Set the other running transaction to aborted if it uses the key
				val row = updateKeyResult.one()

				if (row == null) {
					return Abort(txid, s"table $TABLE_KEYS did not return a result for update query")
				}

				if (!rowWasApplied(row)) {
					//gets the next row in the result set.
					var otherTxId : Id = row.get("txid", runtimeClassOf[Id])

					var retries = 10
					var failed = true

					while (retries > 0) {

						val updateOtherTxResult = session.execute(
							update(TABLE_TX)
								.`with`(set("status", txStatusOps.aborted))
								.where(QueryBuilder.eq("txid", otherTxId))
								.onlyIf(QueryBuilder.ne("status", txStatusOps.committed))
								.setConsistencyLevel(ConsistencyLevel.ALL)
						)

						//4.1.1. If the transaction was already committed then it is save to just change the key
						//4.1.2. If the transaction was not committed (then it has been changed to aborted) and then it is save to just change the key
						val updateKeyAgainResult = session.execute(
							update(TABLE_KEYS)
								.`with`(set("txid", txid))
								.where(QueryBuilder.eq("key", write.key))
								.onlyIf(QueryBuilder.eq("txid", otherTxId))
								.setConsistencyLevel(ConsistencyLevel.ALL)
						)

						val rowAgain = updateKeyAgainResult.one()

						if (rowAgain == null) {
							return Abort(txid, s"table $TABLE_KEYS did not return a result for update query")
						}

						if (rowWasApplied(rowAgain)) {
							retries = 0
							failed = false
						} else {
							//If we could not change the key (because another transaction changed it before us) retry it again
							retries = retries - 1
							otherTxId = rowAgain.get("txid", runtimeClassOf[Id])
						}

					}

					//If we already retried to change the key X times without success, give up
					if (failed) {
						//assert(false, "was unable to lock the key")
						return Abort(txid, s"could not get a lock on key ${write.key}")
					}
				}
			})

			//5. Add the data to the data table
			//5.1. Create fresh ids foir each write
			val deps : List[Id] = writes.map(write => idOps.freshId())
			val depsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(deps.toSet)

			//5.2. Add a transaction record to the data table
			session.execute(
				update(TABLE_DATA)
					.`with`(set("data", null))
					.and(set("deps", depsJava))
					.and(set("txid", txid))
					.and(set("consistency", consistencyLevelOps.sequential))
					.where(QueryBuilder.eq("key", "$trans"))
					.and(QueryBuilder.eq("id", txid))
			)

			//5.3 Add a data entry for each write
			writes.zip(deps).foreach(writeAndId => {
				val (write, id) = writeAndId

				//Convert dependencies to Java
				val writeDepsJava : java.util.Set[Id] = JavaConverters.setAsJavaSet(write.dependencies.union(Set(txid)))

				session.execute(
					update(TABLE_DATA)
						.`with`(set("data", write.data))
						.and(set("deps", writeDepsJava))
						.and(set("txid", txid))
						.and(set("consistency", consistencyLevelOps.sequential))
						.where(QueryBuilder.eq("key", write.key))
						.and(QueryBuilder.eq("id", id))
				)
			})

			//6. Mark transaction as comitted
			val updateTxComittedResult = session.execute(
				update(TABLE_TX)
					.`with`(set("status", txStatusOps.committed))
					.where(QueryBuilder.eq("txid", txid))
					.onlyIf(QueryBuilder.eq("status", txStatusOps.pending))
					.setConsistencyLevel(ConsistencyLevel.ALL)
			)

			if (!updateTxComittedResult.wasApplied()) {
				return Abort(txid, "the transaction has been aborted by a conflicting transaction before being able to commit")
			}

			return Success(txid, deps)
		} catch {
			case e : WriteTimeoutException => e.getWriteType match {
				case WriteType.CAS => return Abort(txid, e.getMessage)
				case _ => return Error(txid, e)
			}
		}
	}



	trait ReadStatus
	object ReadStatus {
		case class Success(key : Key, id : Id, data : Data) extends ReadStatus
		case class NotFound(key : Key, description : String) extends ReadStatus
		case class Abort(key : Key, description : String) extends ReadStatus
		case class Error(key : Key, e : Throwable) extends ReadStatus
	}


	def read(session : Session, key : Key): ReadStatus = {

		import ReadStatus._
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		//Retrieve the maximum id for a given key
		val maxResult = session.execute(select().max("id")
			.from(TABLE_DATA)
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
			.from(TABLE_DATA)
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



		val readTxid = readRow.get("txid", runtimeClassOf[Id])

		//1. If the read value does not belong to a transaction
		if (readTxid == null) {
			return Success(key, readId, readRow.get("data", runtimeClassOf[Data]))
		}

		//2. If txid != null abort the transaction
		val abortTxResult = session.execute(update(TABLE_TX)
			.`with`(set("status", txStatusOps.aborted))
			.where(QueryBuilder.eq("txid", readTxid))
			.onlyIf(QueryBuilder.eq("status", txStatusOps.pending))
			.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val abortTxRow = abortTxResult.one()

		if (abortTxRow == null) {
//			assert(false, "did not retrieve anything from database")
			return Abort(key, s"txid $readTxid has not been found in the transaction table")
		}

		if (rowWasApplied(abortTxRow)) {
			return Success(key, readId, readRow.get("data", runtimeClassOf[Data]))
		}

		//2.1. If the status was not pending, we have to take further actions
		val status = abortTxRow.get("status", runtimeClassOf[TxStatus])

		//If the transaction was committed, remove the transaction tag from the row
		if (status == txStatusOps.committed) {
			session.execute(
				update(TABLE_DATA)
					.`with`(set("txid", null))
					.where(QueryBuilder.eq("id", readId))
					.and(QueryBuilder.eq("key", key))
			)


			return Success(key, readId, readRow.get("data", runtimeClassOf[Data]))
		} else if (status == txStatusOps.aborted) {
			session
				.execute(delete()
					.from(TABLE_DATA)
					.where(QueryBuilder.eq("id", readId))
					.and(QueryBuilder.eq("key", key))
				)

			//Recursively read the next key
			//TODO: Retry only for X times
			return read(session, key)
		}

		//We handled the 3 txstates pending, committed, and aborted. We should never get here.
//		assert(false, "unhandled transaction state: " + status)
		return Error(key, new IllegalStateException("unhandled transaction state: " + status))
	}



}
