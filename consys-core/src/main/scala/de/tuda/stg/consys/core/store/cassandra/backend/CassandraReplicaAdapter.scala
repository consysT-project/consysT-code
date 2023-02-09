package de.tuda.stg.consys.core.store.cassandra.backend

import com.datastax.oss.driver.api.core.{CqlSession, DriverTimeoutException}
import com.datastax.oss.driver.api.core.cql.{BatchStatementBuilder, SimpleStatement}

import java.lang.reflect.Field
import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import com.datastax.oss.driver.api.core.cql.{BatchStatementBuilder, ResultSet, SimpleStatement, Statement}
import com.datastax.oss.driver.api.core.{CqlSession, ConsistencyLevel => CassandraLevel}
import com.datastax.oss.driver.api.querybuilder.QueryBuilder
import com.datastax.oss.driver.api.querybuilder.QueryBuilder.{insertInto, literal}
import com.datastax.oss.driver.api.querybuilder.insert.Insert
import com.datastax.oss.driver.api.querybuilder.select.Selector
import de.tuda.stg.consys.core.store.Triggerable
import de.tuda.stg.consys.core.store.cassandra.backend.trigger.RMIServer
import de.tuda.stg.consys.core.store.utils.Reflect

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, NotSerializableException, ObjectInputStream, ObjectOutputStream}
import java.nio.ByteBuffer
import java.rmi.registry.LocateRegistry
import java.rmi.server.UnicastRemoteObject
import scala.concurrent.TimeoutException
import scala.concurrent.duration.FiniteDuration
import scala.reflect.ClassTag

class RegistryThread() extends Thread {
	override def run(): Unit = {
		val serverURL = s"rmi://127.0.0.1:1234/test"

		//Unicast Remote Object Stub is created and the object is exported to Client through the port number mentioned
		val port = 1234

		try {
			val stub = UnicastRemoteObject.exportObject(RMIServer, port)
			//RMI registry is instantiated
			val registry = LocateRegistry.createRegistry(port)

			//URL is being passed instead of string tag identifier while binding the stub containing the server object to the registry
			registry.rebind(serverURL, stub)
		}
		catch {
			case e: Exception => ()
		}
	}
}

private[cassandra] class CassandraReplicaAdapter(cassandraSession : CqlSession, timeout : FiniteDuration) {
	private val keyspaceName : String = "consys_experimental"
	private val objectTableName : String = "objects"

	val registryThread = new RegistryThread()
	registryThread.start()

	/* Initialize tables, if not available... */
	cassandraSession.execute(s"USE $keyspaceName")
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
		Every entry stores data belonging to an object. There are two possiblities: Either an
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
						 |class text,
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

		// Drop an existing trigger and create a new one

		cassandraSession.execute(
			SimpleStatement.builder(
				s"""DROP TRIGGER IF EXISTS trigger ON $keyspaceName.$objectTableName;""")
				.setExecutionProfileName("consys_init")
				.build()
		)

		cassandraSession.execute(
			SimpleStatement.builder(
				s"""CREATE TRIGGER trigger ON $keyspaceName.$objectTableName USING 'de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaTriggerJava';""")
				.setExecutionProfileName("consys_init")
				.build()
		)

	}

	private final val FIELD_ALL = "$ALL"
	private final val TYPE_FIELD = 1
	private final val TYPE_OBJECT = 2
	private final val CONSISTENCY_ANY = "$ANY"


	private[cassandra] def writeFieldEntry[T <: Serializable](
		batchBuilder : BatchStatementBuilder, // the batch builder that creates the final write statement
		id : String,
		fields : Iterable[Field], // the fields of the object that are written
		obj : T,
		clevel : CassandraLevel
	) : Unit = {
		import com.datastax.oss.driver.api.core.CqlSession


		if (obj.isInstanceOf[Triggerable]) {
			val allFields = obj.getClass.getDeclaredFields

			for (field <- allFields) {
				if (!fields.exists(f => f.getName == field.getName)) {
					field.setAccessible(true)
					val value = field.get(obj).asInstanceOf[Serializable]

					val builder: Insert = insertInto(s"$objectTableName")
						.value("id", literal(id))
						.value("fieldid", literal(field.getName))
						.value("type", literal(TYPE_FIELD))
						.value("consistency", literal(CONSISTENCY_ANY))
						.value("class", literal(obj.getClass.getName))
						.value("state", literal(CassandraReplicaAdapter.serializeObject(value))) // TODO: handle null fields

					val statement = builder.build().setConsistencyLevel(clevel)
					batchBuilder.addStatement(statement)
					field.setAccessible(false)
				}
			}
		}

		for (field <- fields) {
			field.setAccessible(true)
			val builder : Insert = insertInto(s"$objectTableName")
				.value("id", literal(id))
				.value("fieldid", literal(field.getName))
				.value("type", literal(TYPE_FIELD))
				.value("consistency", literal(CONSISTENCY_ANY))
				.value("class", literal(obj.getClass.getName))
				.value("state", literal(CassandraReplicaAdapter.serializeObject(field.get(obj).asInstanceOf[Serializable]))) // TODO: handle null fields

			val statement = builder.build().setConsistencyLevel(clevel)
			batchBuilder.addStatement(statement)
			field.setAccessible(false)
		}
	}

	private[cassandra] def writeObjectEntry[T <: Serializable](
		batchBuilder : BatchStatementBuilder, // the batch builder that creates the final write statement
		id : String,
		obj : T,
		clevel : CassandraLevel
	) : Unit = {
		import QueryBuilder._

		val builder : Insert = insertInto(s"$objectTableName")
			.value("id", literal(id))
			.value("fieldid", literal(FIELD_ALL))
			.value("type", literal(TYPE_OBJECT))
			.value("consistency", literal(CONSISTENCY_ANY))
			.value("state", literal(CassandraReplicaAdapter.serializeObject(obj.asInstanceOf[Serializable])))

		val statement = builder.build().setConsistencyLevel(clevel)
		batchBuilder.addStatement(statement)
	}


	private[cassandra] def executeStatement(statement : Statement[_]) : ResultSet = {
		if (!sessionInitialized) {
			cassandraSession.execute(s"USE $keyspaceName")
			sessionInitialized = true
		}

		cassandraSession.execute(statement)
	}


	private[cassandra] class StoredFieldEntry(
		val addr : String,
		val fields : Map[Field, Any],
		val timestamps : Map[Field, Long]
	)

	private[cassandra] class StoredObjectEntry(
		val addr : String,
		val state : Any,
		val timestamp : Long
	)

	private[cassandra] def readObjectEntry[T <: Serializable : ClassTag](addr : String, clevel : CassandraLevel) : StoredObjectEntry = {
		val query = QueryBuilder.selectFrom(s"$objectTableName")
			.columns("id", "type", "state")
			.function("WRITETIME", Selector.column("state")).as("writetime")
			.whereColumn("id").isEqualTo(QueryBuilder.literal(addr))
			.build()
			//TODO: Read every field with its correct consistency level
			.setConsistencyLevel(clevel)

		//TODO: Add failure handling
		val startTime = System.nanoTime()
		while (System.nanoTime() < startTime + timeout.toNanos) {
			val response = cassandraSession.execute(query)

			response.one() match {
				case null =>  //the address has not been found. retry.
				case row =>
					val typ = row.get("type", TypeCodecs.INT)
					if (typ != TYPE_OBJECT) throw new IllegalStateException(s"expected object stored as whole, but got: $response")

					val obj = CassandraReplicaAdapter.deserializeObject[T](row.get("state", TypeCodecs.BLOB))
					val time = row.get("writetime", TypeCodecs.BIGINT)
					return new StoredObjectEntry(addr, obj, time)
			}
			Thread.sleep(10)
		}

		throw new TimeoutException(s"the object with address $addr has not been found on this replica")
	}

	private[cassandra] def readFieldEntry[T <: Serializable : ClassTag](addr : String, clevel : CassandraLevel) : StoredFieldEntry = {
		val query = QueryBuilder.selectFrom(s"$objectTableName")
			.columns("id", "fieldid", "type", "state")
			.function("WRITETIME", Selector.column("state")).as("writetime")
			.whereColumn("id").isEqualTo(QueryBuilder.literal(addr))
			.build()
			//TODO: Read every field with its correct consistency level
			.setConsistencyLevel(clevel)

		//TODO: Add failure handling
		val startTime = System.nanoTime()
		while (System.nanoTime() < startTime + timeout.toNanos) {
			val response = cassandraSession.execute(query)

			if (response.iterator().hasNext) {
				var fields: Map[Field, Any] = Map.empty
				var timestamps: Map[Field, Long] = Map.empty

				response.forEach(row => {
					val typ = row.get("type", TypeCodecs.INT)
					if (typ != TYPE_FIELD) throw new IllegalStateException(s"expected object stored as fields, but got: $response")

					val fieldName: String = row.get("fieldid", TypeCodecs.TEXT)
					val field: Field = Reflect.getField(implicitly[ClassTag[T]].runtimeClass, fieldName)

					val state: Any = CassandraReplicaAdapter.deserializeObject[Serializable](row.get("state", TypeCodecs.BLOB))
					val timestamp: Long = row.get("writetime", TypeCodecs.BIGINT)

					fields = fields + (field -> state)
					timestamps = timestamps + (field -> timestamp)
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

	private[cassandra] def serializeObject[T <: Serializable](obj : T) : ByteBuffer = {
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

	private[cassandra] def deserializeObject[T <: Serializable](buffer : ByteBuffer) : T = {
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