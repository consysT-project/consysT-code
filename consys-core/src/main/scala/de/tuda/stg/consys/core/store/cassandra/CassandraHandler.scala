package de.tuda.stg.consys.core.store.cassandra

import de.tuda.stg.consys.core.store.Handler
import de.tuda.stg.consys.experimental.lang.store.Handler

import scala.reflect.runtime.universe.TypeTag

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
case class CassandraHandler[T <: java.io.Serializable : TypeTag](obj : CassandraObject[T]) extends Handler[T] {

	override def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R = {
		obj.invoke(methodId, args)
	}

	def getObject : CassandraObject[T] = obj
}
