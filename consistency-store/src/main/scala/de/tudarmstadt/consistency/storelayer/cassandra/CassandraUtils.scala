package de.tudarmstadt.consistency.storelayer.cassandra

import com.datastax.driver.core.{Row, TupleValue}

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
object CassandraUtils {


	private[cassandra] def tupleToCassandraTuple[A,B](tuple : (A,B))(implicit sessionBinding : SessionBinding[_, _, _, _, _, _]) : TupleValue = {
		import sessionBinding._
		import sessionBinding.typeBinding._

		val typ = cluster.getMetadata.newTupleType(TypeCodecs.Id.getCqlType, TypeCodecs.Key.getCqlType)
		typ.newValue(tuple._1.asInstanceOf[AnyRef], tuple._2.asInstanceOf[AnyRef])
	}

	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")
}
