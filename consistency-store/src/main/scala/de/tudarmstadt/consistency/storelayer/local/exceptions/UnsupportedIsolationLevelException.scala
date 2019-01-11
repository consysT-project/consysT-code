package de.tudarmstadt.consistency.storelayer.local.exceptions

/**
	* Created on 28.08.18.
	*
	* @author Mirko Köhler
	*/
class UnsupportedIsolationLevelException[Isolation](val unsupportedIsolationLevel : Isolation) extends Exception(s"isolation level is not supported by the store. found: $unsupportedIsolationLevel") {



}
