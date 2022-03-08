package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import de.tuda.stg.consys.core.store.utils.Reflect
import java.lang.reflect.Field
import scala.reflect.ClassTag


/**
 * Wrapper for objects that have been read from Cassandra.
 */
private[cassandra] abstract class CassandraObject[T <: CassandraStore#ObjType : ClassTag, Level <: CassandraStore#Level] extends ReflectiveObject[CassandraStore#Addr, T] {

	override def addr : CassandraStore#Addr

	override def state : T

	def consistencyLevel : Level

	def fieldLevels : Field => CassandraStore#Level

	def timestamps : Field => Long

	def newestTimestamp : Long

	lazy val fields : Iterable[Field] = Reflect.getFields(implicitly[ClassTag[T]].runtimeClass)

	def toRef : CassandraRef[T] = CassandraRef[T](addr, consistencyLevel)
}
