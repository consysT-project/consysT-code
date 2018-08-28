package de.tudarmstadt.consistency.store.scala.transactions

import com.datastax.driver.core.Row

/**
	* Created on 22.08.18.
	*
	* @author Mirko Köhler
	*/
class CassandraUtils {

	/**
		* Checkes whether a lightweight transaction has been applied given the row
		* of the result.
		*
		* @param row The row that was returned by the lightweight transaction.
		* @return  True, if the transaction has been applied.
		*
		* @see [[com.datastax.driver.core.ResultSet#wasApplied()]]
		*
		*/
	private def lightweightTransactionWasApplied(row : Row) : Boolean =
		row.getBool("[applied]")

}
