package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import de.tuda.stg.consys.core.store.utils.Reflect
import de.tuda.stg.consys.core.store.{ConsistencyLevel, Handler}
import jdk.dynalink.linker.support.TypeUtilities
import scala.reflect.ClassTag
import scala.reflect.runtime.universe._


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
