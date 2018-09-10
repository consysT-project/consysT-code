package de.tudarmstadt.consistency.store

import java.util.UUID

import com.datastax.driver.core.{Cluster, DataType, Row, TupleValue}
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

import scala.collection.JavaConverters
import scala.reflect.runtime.universe._


/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
package object cassandra {

	private[cassandra] def rowWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")

}
