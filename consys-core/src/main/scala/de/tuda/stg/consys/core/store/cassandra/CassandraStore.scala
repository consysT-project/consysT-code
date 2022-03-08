package de.tuda.stg.consys.core.store.cassandra

import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import com.datastax.oss.driver.api.core.cql.{BatchStatementBuilder, ResultSet, SimpleStatement, Statement}
import com.datastax.oss.driver.api.core.{CqlSession, ConsistencyLevel => CassandraLevel}
import com.datastax.oss.driver.api.querybuilder.QueryBuilder
import com.datastax.oss.driver.api.querybuilder.insert.Insert
import com.datastax.oss.driver.api.querybuilder.select.Selector
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.cassandra.CassandraStore.CassandraStoreId
import de.tuda.stg.consys.core.store.extensions.store.{DistributedStore, DistributedZookeeperLockingStore, LockingStore}
import de.tuda.stg.consys.core.store.utils.Reflect
import io.aeron.exceptions.DriverTimeoutException
import java.io._
import java.lang.reflect.Field
import java.net.InetSocketAddress
import java.nio.ByteBuffer
import org.apache.curator.framework.{CuratorFramework, CuratorFrameworkFactory}
import org.apache.curator.retry.ExponentialBackoffRetry
import scala.concurrent.TimeoutException
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.reflect.ClassTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait CassandraStore extends DistributedStore
	with LockingStore {
	/* Force initialization of binding */
	CassandraBinding

	override final type Id = CassandraStoreId

	override final type Addr = String
	override final type ObjType = java.io.Serializable

	override final type TxContext = CassandraTransactionContext

	override final type HandlerType[T <: ObjType] = CassandraHandler[T]
	override final type RefType[T <: ObjType] = CassandraRef[T]

	override final type Level = ConsistencyLevel[CassandraStore]


	protected[store] val cassandraSession : CqlSession

	//This flag states whether the creation should initialize tables etc.
	protected def initializing : Boolean

	override def transaction[U](body : TxContext => Option[U]) : Option[U] = this.synchronized {
		CassandraStores.currentStore.withValue(this) {
			val tx = new CassandraTransactionContext(this)
			CassandraStores.currentTransaction.withValue(tx) {
				try {
					body(tx) match {
						case None => None
						case res@Some(_) =>
							res
					}
				} finally {
					tx.commit()
				}
			}
		}
	}


	override def close(): Unit = {
		super.close()
		cassandraSession.close()
	}

	override def id : CassandraStoreId = CassandraStoreId(s"cassandra-store@${cassandraSession.getContext.getSessionName}")


	/**
	 * This object is used to communicate with Cassandra, i.e. writing and reading data from keys.
	 */
	private[cassandra] final object CassandraBinding {
		private val keyspaceName : String = "consys_experimental"
		private val objectTableName : String = "objects"

		/* Initialize tables, if not available... */
		if (initializing) initialize()
		cassandraSession.execute(s"USE $keyspaceName")

		private def initialize() : Unit = {
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
							 |id text primary key,
							 |fieldid text primary key,
							 |type int,
							 |consistency text,
							 |state blob
							 |) with comment = 'contains the replicated data for a consys execution'"""
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


		private[cassandra] def writeFieldEntry[T <: Serializable](
			batchBuilder : BatchStatementBuilder, // the batch builder that creates the final write statement
			id : String,
			fields : Iterable[Field], // the fields of the object that are written
			obj : T,
			clevel : CassandraLevel
		) : Unit = {
			import QueryBuilder._

			for (field <- fields) {
				val builder : Insert = insertInto(s"$objectTableName")
					.value("id", literal(id))
					.value("fieldid", literal(field.getName))
					.value("type", literal(TYPE_FIELD))
					.value("consistency", literal(CONSISTENCY_ANY))
					.value("state", literal(CassandraStore.serializeObject(field.get(obj).asInstanceOf[Serializable])))

				val statement = builder.build().setConsistencyLevel(clevel)
				batchBuilder.addStatement(statement)
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
				.value("state", literal(CassandraStore.serializeObject(obj.asInstanceOf[Serializable])))

			val statement = builder.build().setConsistencyLevel(clevel)
			batchBuilder.addStatement(statement)
		}


		private[cassandra] def executeStatement(statement : Statement[_]) : ResultSet = {
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

						val obj = CassandraStore.deserializeObject[T](row.get("state", TypeCodecs.BLOB))
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

				var fields : Map[Field, Any] = Map.empty
				var timestamps : Map[Field, Long] = Map.empty

				val response = cassandraSession.execute(query)

				response.forEach(row => {
					val typ = row.get("type", TypeCodecs.INT)
					if (typ != TYPE_FIELD) throw new IllegalStateException(s"expected object stored as fields, but got: $response")

					val fieldName : String = row.get("fieldid", TypeCodecs.TEXT)
					val field : Field = Reflect.getField(implicitly[ClassTag[T]].runtimeClass, fieldName)

					val state : Any = CassandraStore.deserializeObject[Serializable](row.get("state", TypeCodecs.BLOB))
					val timestamp : Long = row.get("writetime", TypeCodecs.BIGINT)

					fields = fields + (field -> state)
					timestamps = timestamps + (field -> timestamp)
				})

				return new StoredFieldEntry(addr, fields, timestamps)

				Thread.sleep(10)
			}
			throw new TimeoutException(s"the object with address $addr has not been found on this replica")
		}
	}


}

object CassandraStore {

	case class CassandraStoreId(name : String)


	case class AddrNotAvailableException(addr : String) extends Exception(s"address <$addr> not available")

	def fromAddress(host : String, cassandraPort : Int, zookeeperPort : Int, withTimeout : FiniteDuration = Duration(10, "s"), withInitialize : Boolean = false) : CassandraStore = {

		class CassandraStoreImpl(
			override val cassandraSession : CqlSession,
			override val curator : CuratorFramework,
			override val timeout : FiniteDuration,
			override val initializing : Boolean
    ) extends CassandraStore with DistributedZookeeperLockingStore

		val cassandraSession = CqlSession.builder()
			.addContactPoint(InetSocketAddress.createUnresolved(host, cassandraPort))
			.withLocalDatacenter("datacenter1")
			.build()

		val curator = CuratorFrameworkFactory
			.newClient(s"$host:$zookeeperPort", new ExponentialBackoffRetry(250, 3))

		new CassandraStoreImpl(
			cassandraSession,
			curator,
			timeout = withTimeout,
			initializing = withInitialize
		)
	}


	/* Helper methods */

	private[CassandraStore] def serializeObject[T <: Serializable](obj : T) : ByteBuffer = {
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

	private[CassandraStore] def deserializeObject[T <: Serializable](buffer : ByteBuffer) : T = {
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
