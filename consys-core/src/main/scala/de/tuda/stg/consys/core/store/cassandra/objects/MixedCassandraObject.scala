package de.tuda.stg.consys.core.store.cassandra.objects

import de.tuda.stg.consys.core.store.cassandra.levels.Mixed
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import de.tuda.stg.consys.core.store.cassandra.objects.MixedCassandraObject.FetchedLevel
import java.lang.reflect.Field
import scala.reflect.ClassTag

class MixedCassandraObject[T <: CassandraStore#ObjType : ClassTag](
	override val addr : CassandraStore#Addr,
	override val state : T,
	override val fieldLevels : Map[Field, CassandraStore#Level],
	override val timestamps : Map[Field, Long],
	val readLevel : FetchedLevel
)	extends CassandraObject[T, Mixed.type] {
	override def consistencyLevel : Mixed.type = Mixed

	override lazy val newestTimestamp : Long = timestamps.values.max
}

object MixedCassandraObject {
	sealed trait FetchedLevel
	case object FetchedWeak extends FetchedLevel
	case object FetchedStrong extends FetchedLevel
}
