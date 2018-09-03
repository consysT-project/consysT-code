package de.tudarmstadt.consistency.store.scala.extra

import com.datastax.driver.core.{ResultSet, Row}
import de.tudarmstadt.consistency.store.scala.extra.shim.EventOrdering.{Tx, Update}

import scala.collection.JavaConverters

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
trait RowConverter[T] {

	def convertRow(row : Row) : T

	def resultSetForeach[U](results : ResultSet, f : T => U) : Unit = {
		var row = results.one()

		while (row != null) {
			f(convertRow(row))
			row = results.one()
		}

	}

}
