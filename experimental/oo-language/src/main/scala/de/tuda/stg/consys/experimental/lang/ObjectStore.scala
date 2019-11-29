package de.tuda.stg.consys.experimental.lang

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, NotSerializableException, ObjectInputStream, ObjectOutputStream, Serializable}
import java.net.InetSocketAddress
import java.nio.ByteBuffer
import java.util.concurrent.ConcurrentMap

import com.datastax.oss.driver.api.core.CqlSession
import com.datastax.oss.driver.api.core.`type`.codec.TypeCodecs

import scala.collection.convert.Wrappers.ConcurrentMapWrapper
import scala.collection.mutable

/**
 * Created on 29.11.19.
 *
 * @author Mirko Köhler
 */
trait ObjectStore[Addr, Obj] {

	/**
	 * Binds a new element in the store.
	 *
	 * @param addr The address of the new object.
	 * @param obj The new object.
	 */
	def bind(addr : Addr, obj : Obj) : Unit

	/**
	 * Looks up an element in the store.
	 *
	 * @param addr The address to lookup in the store.
	 * @return The object at the specified location
	 */
	def lookup(addr : Addr) : Obj
}

object ObjectStore {

	class MapStore[Addr, Obj] extends ObjectStore[Addr, Obj] {
		private val store : scala.collection.concurrent.Map[Addr, Obj] =
			scala.collection.concurrent.TrieMap.empty

		override def bind(addr : Addr, obj : Obj) : Unit = store.put(addr, obj)

		override def lookup(addr : Addr) : Obj = store(addr)

		override def toString : String = s"MapStore($store)"
	}

	class CassandraStore[Addr, Obj <: Serializable](address : InetSocketAddress = new InetSocketAddress("127.0.0.1", 9042), reset : Boolean = false) extends ObjectStore[Addr, Obj] {

		private val session = CqlSession.builder
//			.addContactPoint(address)
//  		.withLocalDatacenter("consys-cluster")
			.build

		if (reset) reset() else initialize()

		override def bind(addr : Addr, obj : Obj) : Unit = {
			import com.datastax.oss.driver.api.querybuilder.QueryBuilder._

			val query = insertInto("consys_blobs")
				.value("addr", literal(addr.toString))
				.value("object", literal(serializeObject(obj)))

			session.execute(query.build())
		}

		override def lookup(addr : Addr) : Obj = {
			import com.datastax.oss.driver.api.querybuilder.QueryBuilder._

			val query = selectFrom("consys_blobs")
  			.column("object")
  			.whereColumn("addr").isEqualTo(literal(addr.toString))

			val results = session.execute(query.build())
			val buffer = results.one().get("object", TypeCodecs.BLOB)
			deserializeObject[Obj](buffer)
		}

		def reset() : Unit = {
			session.execute("drop keyspace if exists consys")
			initialize()
		}


		/* Helper methods */

		private def initialize() : Unit = {
			/* Initialize tables, if not available... */
			session.execute(
				"""create keyspace if not exists consys
					|with replication = {'class': 'SimpleStrategy', 'replication_factor' : 3}""".stripMargin)
			session.execute("use consys")
			session.execute(
				"""create table if not exists consys_blobs (
					|addr text primary key,
					|object blob
					|) with comment = 'stores objects as blobs'
					|""".stripMargin
			)
		}

		private def serializeObject[T <: Serializable](obj : T) : ByteBuffer = {
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

		private def deserializeObject[T <: Serializable](buffer : ByteBuffer) : T = {
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

}
