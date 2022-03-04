package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import scala.reflect.ClassTag


/**
 * Wrapper for objects that have been read from Cassandra.
 */
private[cassandra] class CassandraObject[T <: CassandraStore#ObjType : ClassTag, Level <: CassandraStore#Level](
	override val addr : CassandraStore#Addr,
	override val state : T,
	/** The consistency level of the object. */
	val consistencyLevel : Level,
	/** The timestamp of the object when read from Cassandra, or -1 if the object was not read */
	val timestamp : Long
) extends ReflectiveObject[CassandraStore#Addr, T] {
	def toRef : CassandraRef[T] = CassandraRef[T](addr, consistencyLevel)
}
