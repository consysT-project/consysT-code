package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import scala.reflect.ClassTag


/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
private[cassandra] class CassandraObject[T <: CassandraStore#ObjType : ClassTag, Level <: CassandraStore#Level](
	override val addr : CassandraStore#Addr,
	override val state : T,
	val consistencyLevel : Level
) extends ReflectiveObject[CassandraStore#Addr, T] {
	def toRef : CassandraRef[T] = CassandraRef[T](addr, consistencyLevel)
}
