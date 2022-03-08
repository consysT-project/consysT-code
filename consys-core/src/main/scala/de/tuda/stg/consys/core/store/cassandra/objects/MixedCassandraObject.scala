package de.tuda.stg.consys.core.store.cassandra.objects

import de.tuda.stg.consys.core.store.cassandra.levels.Mixed
import de.tuda.stg.consys.core.store.cassandra.{CassandraObject, CassandraStore}
import java.lang.reflect.Field
import scala.reflect.ClassTag

class MixedCassandraObject[T <: CassandraStore#ObjType : ClassTag](
	override val addr : CassandraStore#Addr,
	override val state : T,
	override val fieldLevels : Map[Field, CassandraStore#Level],
	override val timestamps : Map[Field, Long]
)	extends CassandraObject[T, Mixed.type] {
	override def consistencyLevel : Mixed.type = Mixed

	override lazy val newestTimestamp : Long = timestamps.values.max

}
