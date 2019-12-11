package de.tuda.stg.consys.experimental.lang.store.cassandra

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
class WeakCassandraObject[T <: Serializable : TypeTag](addr : String, state : T) extends CassandraObject(addr, state) {



}
