package de.tudarmstadt.consistency.store.scala.cassandra

import java.io.{ByteArrayInputStream, ByteArrayOutputStream, ObjectInputStream, ObjectOutputStream}
import java.util.UUID

import com.datastax.driver.core.ConsistencyLevel
import de.tudarmstadt.consistency.store.scala.impl.ReadWriteRef

trait CassandraRef[Key <: UUID, T] extends ReadWriteRef[Key, T] {
		val key : Key
		val consistencyLevel : ConsistencyLevel
		val store : CassandraBlobStore[Key, _ >: T]


		override protected def handleRead() : Option[T] = {
			val data = store.table.readWithConsistencyLevel(key, consistencyLevel)

			if (data == null) return None

			val bis = new ByteArrayInputStream(data)
			val ois = new ObjectInputStream(bis)

			//TODO: Handle exceptions
			val o = ois.readObject

			Some(o.asInstanceOf[T])
		}

		override protected def handleWrite(value : T) : Unit = {
			val bos = new ByteArrayOutputStream
			val oos = new ObjectOutputStream(bos)

			//Transform object into a string representation
			oos.writeObject(value)
			oos.flush()

			val data = bos.toByteArray

			store.table.writeWithConsistencyLevel(key, data, consistencyLevel)
		}


	}

	class OneRef[Key <: UUID, T](override val store : CassandraBlobStore[Key, _ >: T], override val key : Key) extends CassandraRef[Key, T] {
		override val consistencyLevel : ConsistencyLevel = ConsistencyLevel.ONE
	}

	class QuorumRef[Key <: UUID, T](override val store : CassandraBlobStore[Key, _ >: T], override val key : Key) extends CassandraRef[Key, T] {
		override val consistencyLevel : ConsistencyLevel = ConsistencyLevel.QUORUM
	}

	class AllRef[Key <: UUID, T](override val store : CassandraBlobStore[Key, _ >: T], override val key : Key) extends CassandraRef[Key, T] {
		override val consistencyLevel : ConsistencyLevel = ConsistencyLevel.ALL
	}