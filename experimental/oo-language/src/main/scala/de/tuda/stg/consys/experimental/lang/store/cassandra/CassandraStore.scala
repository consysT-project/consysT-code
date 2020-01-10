package de.tuda.stg.consys.experimental.lang.store.cassandra

import java.io._
import java.net.InetSocketAddress
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit

import com.datastax.oss.driver.api.core.CqlSession
import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs
import com.datastax.oss.driver.api.core.cql.{BatchStatement, BatchType}
import com.datastax.oss.driver.api.querybuilder.QueryBuilder
import de.tuda.stg.consys.core.Address
import de.tuda.stg.consys.experimental.lang.store.Store

import scala.concurrent.TimeoutException
import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.reflect.runtime.universe.TypeTag


/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait CassandraStore extends Store
	with ZookeeperStoreExt {
//	def this(host : String, port : Int) = this(CqlSession.builder()
//		.addContactPoint(InetSocketAddress.createUnresolved(host, port))
//    .withLocalDatacenter("datacenter1")
//		.build()
//	)

	override final type Addr = String
	override final type ObjType = Any with java.io.Serializable

	override final type Context = CassandraTxContext

	override final type RefType[T <: ObjType] = CassandraHandler[T]

	protected val session : CqlSession
	protected def timeout : FiniteDuration

	//This flag states whether the creation should initialize tables etc.
	protected def initializing : Boolean

	override def transaction[T](code : Context => Option[T]) : Option[T] = {
		val tx = CassandraTxContext(this)
		code(tx) match {
			case None => None
			case res@Some(_) =>
				tx.commit()
				res
		}
	}

	override def close(): Unit = {
		super.close()
		session.close()
	}

	override def name : String = s"node@${session.getContext.getSessionName}"


	object CassandraBinding {
		private val keyspaceName : String = "consys_experimental"
		private val objectTableName : String = "objects"

		/* Initialize tables, if not available... */
		if (initializing) initialize()
		session.execute(s"USE $keyspaceName")


		private def initialize(): Unit = {
			session.execute(s"""DROP KEYSPACE IF EXISTS $keyspaceName""")
			session.execute(
				s"""CREATE KEYSPACE $keyspaceName
					 |with replication = {'class': 'SimpleStrategy', 'replication_factor' : 3}"""
					.stripMargin
			)
			session.execute(
				s"""CREATE TABLE IF NOT EXISTS $keyspaceName.$objectTableName (
					 |addr text primary key,
					 |state blob
					 |) with comment = 'stores objects as blobs'"""
					.stripMargin
			)
		}

		private[cassandra] def writeObject[T <: Serializable](addr : String, obj : T, clevel : CLevel) : Unit = {
			import QueryBuilder._

			val query = insertInto(s"$objectTableName")
				.value("addr", literal(addr))
				.value("state", literal(CassandraStore.serializeObject(obj)))
				.build()
				.setConsistencyLevel(clevel)

			//TODO: Add failure handling
			session.execute(query)
		}

		private[cassandra] def writeObjects(objs : Iterable[(String, _)], clevel : CLevel) : Unit = {
			import QueryBuilder._
			val batch = BatchStatement.builder(BatchType.LOGGED)

			for (obj <- objs) {
				val query = insertInto(s"$objectTableName")
					.value("addr", literal(obj._1))
					.value("state", literal(CassandraStore.serializeObject(obj._2.asInstanceOf[Serializable])))
					.build()
					.setConsistencyLevel(clevel)

				batch.addStatement(query)
			}

			//TODO: Add failure handling
			session.execute(batch.build().setConsistencyLevel(clevel))
		}


		private[cassandra] def readObject[T <: Serializable : TypeTag](addr : String, clevel : CLevel) : T = {
			import QueryBuilder._

			val query = selectFrom(s"$objectTableName")
				.all()
				.whereColumn("addr").isEqualTo(literal(addr))
				.build()
				.setConsistencyLevel(clevel)

			//TODO: Add failure handling
			val startTime = System.nanoTime()
			while (System.nanoTime() < startTime + timeout.toNanos) {
				val response = session.execute(query)

				response.one() match {
					case null =>  //the address has not been found. retry.
					case row =>
						return CassandraStore.deserializeObject[T](row.get("state", TypeCodecs.BLOB))
				}

				Thread.sleep(200)
			}

			throw new TimeoutException(s"the object with address $addr has not been found on this replica")

		}
	}


}

object CassandraStore {

	case class AddrNotAvailableException(addr : String) extends Exception(s"address <$addr> not available")

	def fromAddress(host : String, cassandraPort : Int, zookeeperPort : Int, withTimeout : FiniteDuration = Duration(10, "s"), withInitialize : Boolean = false) : CassandraStore = {
		new CassandraStore {
			override protected val session : CqlSession = CqlSession.builder()
					.addContactPoint(InetSocketAddress.createUnresolved(host, cassandraPort))
			    .withLocalDatacenter("datacenter1")
					.build()
			override protected def timeout : FiniteDuration = withTimeout
			override def zookeeperServer : Address = Address(host, zookeeperPort)
			override protected def initializing : Boolean = withInitialize
		}
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
