package de.tuda.stg.consys.core.store.binding

import de.tuda.stg.consys.core.{ConsistencyLabel, Ref, ReplicatedObject}
import de.tuda.stg.consys.core.store.cassandra.{CassandraHandler, CassandraStore}

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
class CassandraRef[T <: java.io.Serializable](
	override val addr : CassandraStore#Addr,
	override val consistencyLevel : ConsistencyLabel = ???
) extends Ref[CassandraStore#Addr, T] {

	type ConsistencyLevel = ConsistencyLabel

	private val handler : CassandraHandler[T] = ???

	override def deref : ReplicatedObject[String, T] = ???
	override def isAvailable : Boolean = ???
	override def await() : Unit = ???
	override def delete() : Unit = ???
}
