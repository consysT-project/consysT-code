package de.tudarmstadt.consistency.store.cassandra.exceptions

/**
	* Created on 28.08.18.
	*
	* @author Mirko Köhler
	*/
class UnsupportedConsistencyLevelException[Consistency](val unsupportedConsistencyLevel : Consistency) extends Exception(s"consistency level is not supported by the store. found: $unsupportedConsistencyLevel") {



}
