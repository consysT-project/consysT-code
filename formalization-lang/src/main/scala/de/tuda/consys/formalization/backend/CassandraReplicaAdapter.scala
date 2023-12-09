package de.tuda.consys.formalization.backend

import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import com.datastax.oss.driver.api.core.cql.{BatchStatementBuilder, ResultSet, SimpleStatement, Statement}
import com.datastax.oss.driver.api.core.{CqlSession, DriverTimeoutException, ConsistencyLevel => CassandraLevel}
import com.datastax.oss.driver.api.querybuilder.QueryBuilder
import com.datastax.oss.driver.api.querybuilder.QueryBuilder.{insertInto, literal}
import com.datastax.oss.driver.api.querybuilder.insert.Insert
import com.datastax.oss.driver.api.querybuilder.select.Selector
import com.datastax.oss.driver.api.querybuilder.term.Term
import de.tuda.consys.formalization.lang.FieldId
import de.tuda.stg.consys.core.store.utils.Reflect

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, NotSerializableException, ObjectInputStream, ObjectOutputStream}
import java.lang.reflect.Field
import java.nio.ByteBuffer
import scala.concurrent.TimeoutException
import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters._
import scala.reflect.ClassTag

/**
 * This object is used to communicate with Cassandra, i.e. writing and reading data from keys.
 */
class CassandraReplicaAdapter(cassandraSession : CqlSession, timeout : FiniteDuration) {
	private val keyspaceName : String = "consys_experimental"
	private val objectTableName : String = "objects"

	private var sessionInitialized : Boolean = false

	/**
	 * (Re-)creates keyspace and tables, dropping previous data if it exists.
	 */
	def setup() : Unit = {
		try {
			cassandraSession.execute(
				SimpleStatement.builder(s"""DROP KEYSPACE IF EXISTS $keyspaceName""")
					.setExecutionProfileName("consys_init")
					.build()
			)
		} catch {
			case e : DriverTimeoutException =>
				e.printStackTrace()
		}

		cassandraSession.execute(
			SimpleStatement.builder(
				s"""CREATE KEYSPACE $keyspaceName
					 |WITH REPLICATION = {'class': 'SimpleStrategy', 'replication_factor' : 3}"""
					.stripMargin)
				.setExecutionProfileName("consys_init")
				.build()
		)

		/*
		Table layout:
		Every entry stores data belonging to an object. There are two possibilities: Either an
		entry stores the value of one field of an object, or it stores the whole object.

		id : the address of the object, aka the objects name
		fieldid : the name of the field that is stored in the entry, or $ALL if the entry stores a complete object
		type : the type of entry, 1 if it is a field, 2 if it is a whole object
		consistency : the consistency level of the entry, e.g., STRONG or WEAK
		state : the stored data
		 */
		try {
			cassandraSession.execute(
				SimpleStatement.builder(
					s"""CREATE TABLE $keyspaceName.$objectTableName (
						 |id text,
						 |fieldid text,
						 |type int,
						 |consistency text,
						 |state blob,
						 |PRIMARY KEY (id, fieldid)
						 |) WITH COMMENT = 'contains the replicated data for a consys execution'"""
						.stripMargin)
					.setExecutionProfileName("consys_init")
					.build()
			)
		} catch {
			case e : DriverTimeoutException =>
				e.printStackTrace()
		}
	}

	private final val FIELD_ALL = "$ALL"
	private final val TYPE_FIELD = 1
	private final val TYPE_OBJECT = 2
	private final val CONSISTENCY_ANY = "$ANY"


	def writeFieldEntry(
		batchBuilder : BatchStatementBuilder, // the batch builder that creates the final write statement
		id : String,
		fields : Iterable[FieldId], // the fields of the object that are written
		obj : ReplicatedState,
		clevel : CassandraLevel
	) : Unit = {

		for (field <- fields) {
			val builder : Insert = insertInto(s"$objectTableName")
				.value("id", literal(id))
				.value("fieldid", literal(field))
				.value("type", literal(TYPE_FIELD))
				.value("consistency", literal(CONSISTENCY_ANY))
				.value("state", literal(CassandraReplicaAdapter.serializeObject(obj.fields(field).asInstanceOf[Serializable])))

			val statement = builder.build().setConsistencyLevel(clevel)
			batchBuilder.addStatement(statement)
		}
	}

	def executeStatement(statement : Statement[_]) : ResultSet = {
		if (!sessionInitialized) {
			cassandraSession.execute(s"USE $keyspaceName")
			sessionInitialized = true
		}

		cassandraSession.execute(statement)
	}


	class StoredFieldEntry(
		val addr : String,
		val fields : Map[FieldId, Any],
		val timestamps : Map[FieldId, Long]
	)

	/**
	 * Reads an object that was stored with the row-per-field schema.
	 */
	def readFieldEntry(addr: String, fields: Iterable[FieldId], clevel: CassandraLevel): StoredFieldEntry = {
		val query = QueryBuilder.selectFrom(s"$objectTableName")
			.columns("id", "fieldid", "type", "state")
			.function("WRITETIME", Selector.column("state")).as("writetime")
			.whereColumn("id").isEqualTo(QueryBuilder.literal(addr))
			.whereColumn("fieldid").in(fields.map(f => QueryBuilder.literal(f)).asInstanceOf[Iterable[Term]].asJava)
			.build()
			//TODO: Read every field with its correct consistency level (necessary?)
			.setConsistencyLevel(clevel)

		//TODO: Add failure handling
		val startTime = System.nanoTime()
		while (System.nanoTime() < startTime + timeout.toNanos) {
			val response = executeStatement(query)

			if (response.iterator().hasNext) {
				var fields: Map[FieldId, Any] = Map.empty
				var timestamps: Map[FieldId, Long] = Map.empty

				response.forEach(row => {
					val typ = row.get("type", TypeCodecs.INT)
					if (typ != TYPE_FIELD) throw new IllegalStateException(s"expected object stored as fields, but got: $response")

					val fieldName: String = row.get("fieldid", TypeCodecs.TEXT)

					val state: Any = CassandraReplicaAdapter.deserializeObject[Serializable](row.get("state", TypeCodecs.BLOB))
					val timestamp: Long = row.get("writetime", TypeCodecs.BIGINT)

					fields = fields + (fieldName -> state)
					timestamps = timestamps + (fieldName -> timestamp)
				})

				return new StoredFieldEntry(addr, fields, timestamps)
			}

			// the address has not been found. retry.
			Thread.sleep(10)
		}
		throw new TimeoutException(s"the object with address $addr has not been found on this replica")
	}
}

object CassandraReplicaAdapter {

	/* Helper methods */

	private[CassandraReplicaAdapter] def serializeObject[T <: Serializable](obj : T) : ByteBuffer = {
		require(obj != null)

		val bytesOut = new ByteArrayOutputStream()
		val oos = new ObjectOutputStream(bytesOut)
		try {
			oos.writeObject(obj)
			oos.flush()
			return ByteBuffer.wrap(bytesOut.toByteArray)
		} finally {
			bytesOut.close()
			oos.close()
		}
		throw new NotSerializableException(obj.getClass.getName)
	}

	private[CassandraReplicaAdapter] def deserializeObject[T <: Serializable](buffer : ByteBuffer) : T = {
		require(buffer != null)

		val bytesIn = new ByteArrayInputStream(buffer.array())
		val ois = new ObjectInputStream(bytesIn)

		try {
			return ois.readObject().asInstanceOf[T]
		} finally {
			bytesIn.close()
			ois.close()
		}
		throw new NotSerializableException()
	}
}
