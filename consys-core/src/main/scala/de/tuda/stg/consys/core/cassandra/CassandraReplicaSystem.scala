package de.tuda.stg.consys.core.cassandra

import java.io.{ByteArrayOutputStream, NotSerializableException, ObjectOutputStream, Serializable}
import java.nio.ByteBuffer

import com.datastax.oss.driver.api.core.CqlSession
import de.tuda.stg.consys.core
import de.tuda.stg.consys.core.{ConsistencyLevel, ReplicaSystem}
import de.tuda.stg.consys.experimental.lang.LangBinding

import scala.concurrent.duration.FiniteDuration
import scala.reflect.runtime.universe._

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
trait CassandraReplicaSystem extends ReplicaSystem {
	/**
	 * Type for objects that can be stored in the store.
	 */
	override type Obj = LangBinding.Obj

	/**
	 * Type of addresses for unique specifying replicated objects.
	 */
	override final type Addr = String

	/**
	 * Type of references to replicated objects.
	 *
	 * @tparam T The type that is referenced.
	 */
	override type Ref[T <: Obj] = CassandraRef[Addr, T]

	/**
	 * The name of the replica system.
	 *
	 * @return Non-null name of the replica system.
	 */
	override val name : String = s"cassandra-sys-${(scala.math.random() * 12337).toInt}"


	def defaultTimeout : FiniteDuration

	/**
	 * The cql session that is used for this replica system.
	 * @return
	 */
	def cqlSession : CqlSession


	/* Initialize tables, if not available... */
	cqlSession.execute(
		"""create keyspace if not exists consys
			|with replication = {'class': 'SimpleStrategy', 'replication_factor' : 3}""".stripMargin)
	cqlSession.execute("use consys")
	cqlSession.execute(
		"""create table if not exists consys_blobs (
			|addr text primary key,
			|object blob
			|) with comment = 'stores objects as blobs'
			|""".stripMargin
	)




	/**
	 * Creates a new distributed object in this store and returns a reference to that object.
	 * The object can be referenced by other nodes using a path generated from the specified address.
	 *
	 * @param addr The (distributed) address of the object
	 * @param obj  The object to distribute
	 * @return A reference to the created object
	 */
	override def replicate[T <: Obj : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T] = {
		import com.datastax.oss.driver.api.querybuilder.QueryBuilder._

		val query = insertInto("consys_blobs")
  			.value("addr", literal(addr))
  			.value("object", literal(serializeObject(obj)))

		cqlSession.execute(query.build())

		CassandraRef[Addr, T](addr, l, this)
	}

	override def replicate[T <: Obj : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T] = ???

	override def lookup[T <: Obj : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T] = ???

	override def close() : Unit = {
		cqlSession.close()
	}



	/* Helper methods */
	private def serializeObject(obj : Any with Serializable) : ByteBuffer = {
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

}
