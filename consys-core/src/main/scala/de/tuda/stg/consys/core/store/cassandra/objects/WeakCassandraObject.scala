package de.tuda.stg.consys.core.store.cassandra.objects

import de.tuda.stg.consys.core.store.cassandra.levels.Weak
import de.tuda.stg.consys.core.store.cassandra.CassandraStore
import java.lang.reflect.Field
import scala.reflect.ClassTag

class WeakCassandraObject[T <: CassandraStore#ObjType : ClassTag](
	override val addr : CassandraStore#Addr,
	override val state : T,
	val timestamp : Long
) extends CassandraObject[T, Weak.type] {
	override def consistencyLevel : Weak.type = Weak

	override def fieldLevels : Map[Field, CassandraStore#Level] = Map.empty
	override def timestamps : Field => Long = f => timestamp

	override def newestTimestamp : Long = timestamp
}
