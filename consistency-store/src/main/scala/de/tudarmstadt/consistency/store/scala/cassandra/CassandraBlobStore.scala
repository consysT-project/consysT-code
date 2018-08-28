package de.tudarmstadt.consistency.store.scala.cassandra

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, ObjectInputStream, ObjectOutputStream}
import java.lang.annotation.Annotation
import java.nio.ByteBuffer
import java.util
import java.util.{List, UUID}

import com.datastax.driver.core.querybuilder.QueryBuilder.{eq, insertInto, select}
import com.datastax.driver.core.{Session, _}
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.checker.qual.{Strong, Weak}
import de.tudarmstadt.consistency.store.cassandra.CassandraDatabase
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteStore

/**
	* Created on 10.08.18.
	*
	* @author Mirko Köhler
	*/
class CassandraBlobStore[Key <: UUID, Val](val session : com.datastax.driver.core.Session) extends ReadWriteStore[Key, Val, Class[_ <: Annotation]]{


	val table = new CassandraBlobTable("blobdata")


	override type Context = CassandraSessionContext



	override def newSessionContext(): Context =
		new CassandraSessionContext


	private[cassandra] def createTable(): Unit = {
		table.create()
	}

	override def close() : Unit = {
		session.close()
		session.getCluster.close()
	}


	class CassandraSessionContext extends ReadWriteSessionContext {

		override def obtain[T <: Val](key: Key, consistencyLevel : Class[_ <: Annotation]): CassandraRef[Key, T] = consistencyLevel match {
			case x if classOf[Weak] == x => new OneRef[Key, T](CassandraBlobStore.this, key)
			case x if classOf[Strong] == x => new AllRef(CassandraBlobStore.this, key)

			case x => throw new IllegalArgumentException(s"unsupported consistency level. expected Weak or Strong, but got $x")
		}
	}



	class CassandraBlobTable(val tableName : String) {

		private val keyName : String = "id"
		private val dataName : String = "data"

		def create() : Unit = {
			session.execute("DROP TABLE IF EXISTS " + tableName)
			session.execute("CREATE TABLE " + tableName + " (" + keyName + " uuid PRIMARY KEY, " + dataName + " blob);")
		}


		def readWithConsistencyLevel(key : Key, consistencyLevel : ConsistencyLevel) : Array[Byte] = { //Retrieve all elements with key from the database
			val result : ResultSet = session.execute(
				select
					.from(tableName)
					.where(QueryBuilder.eq(keyName, key))
					.setConsistencyLevel(consistencyLevel)
			)

			val rows : util.List[Row] = result.all

			if (rows.isEmpty)
				return null
			else if (rows.size > 1)
				throw new IllegalStateException("can not retrieve more than 1 row, but got:\n" + rows)
			//else rows.size() == 1

			val buffer : ByteBuffer = rows.get(0).get(dataName, classOf[ByteBuffer])


			buffer.array


			/*
			Notice when using foreign keys:

			The read array does contain no link to the database in handles.
			Set the databases of handles when the object has been de-serialized.
			*/
		}

		def writeWithConsistencyLevel(key : Key, bytes : Array[Byte], consistencyLevel : ConsistencyLevel) : Unit = {
			val data : ByteBuffer = ByteBuffer.wrap(bytes)
			//Store object in database
			session.execute(//Upsert operation: if the row already exists, then it is updated. Does not provide any concurrency control.
				insertInto(tableName)
					.values(Array[String](keyName, dataName), Array[AnyRef](key, data))
					.setConsistencyLevel(consistencyLevel))
		}

	}
}


object CassandraBlobStore {


	def create[Key <: UUID, Val](address: String, port: Int, keyspaceName: String, replicationFactor: Int): CassandraBlobStore[Key, Val] = {

		//Initialize a new keyspace
		val cluster = Cluster.builder.addContactPoint(address).withPort(port).build
		val localSession: Session = cluster.newSession

		//Strategy NetworkTopologyStrategy does not support a replication factor.
		val replicationStrategy = "SimpleStrategy"

		localSession.execute("DROP KEYSPACE IF EXISTS " + keyspaceName)
		localSession.execute("CREATE KEYSPACE " + keyspaceName + " WITH replication = {" + "'class':'" + replicationStrategy + "'," + "'replication_factor':" + replicationFactor + "};")

		val session = cluster.connect(keyspaceName)

		val store = new CassandraBlobStore[Key, Val](session)
		store.createTable()

		store
	}

	def local[Key <: UUID, Val](replicationFactor: Int) : CassandraBlobStore[Key, Val] = { //Other possible address: localhost
		create("127.0.0.1", 9042, "local", replicationFactor)
	}




}

