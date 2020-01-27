package de.tuda.stg.consys.core.store.binding

import de.tuda.stg.consys.core.store.cassandra.{CassandraHandler, CassandraStore}
import de.tuda.stg.consys.core.{ConsistencyLabel, ReplicaSystem}

import scala.concurrent.duration.{Duration, FiniteDuration}
import scala.reflect.runtime.universe._

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
class CassandraReplicaSystem(host : String, cassandraPort : Int, zookeeperPort : Int, withTimeout : FiniteDuration = Duration(10, "s"), withInitialize : Boolean = false)  extends ReplicaSystem {

	override type Obj = CassandraStore#ObjType
	override type Addr = CassandraStore#Addr

	override type Ref[T <: Obj] = CassandraRef[T]


	private val store : CassandraStore = CassandraStore.fromAddress(host, cassandraPort, zookeeperPort, withTimeout, withInitialize)

	override def name : String = store.name


	override def replicate[T <: Obj : TypeTag](addr : Addr, obj : T, l : ConsistencyLevel) : Ref[T] = ???

	override def replicate[T <: Obj : TypeTag](obj : T, l : ConsistencyLevel) : Ref[T] = ???


	override def lookup[T <: Obj : TypeTag](addr : Addr, l : ConsistencyLevel) : Ref[T] = ???


	override def close() : Unit = ???
}

