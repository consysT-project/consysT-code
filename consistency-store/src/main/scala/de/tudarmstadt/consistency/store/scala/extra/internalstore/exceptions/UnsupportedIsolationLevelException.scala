package de.tudarmstadt.consistency.store.scala.extra.internalstore.exceptions

/**
	* Created on 28.08.18.
	*
	* @author Mirko Köhler
	*/
class UnsupportedIsolationLevelException[Isolation](val unsupportedIsolationLevel : Isolation) extends Exception(s"isolation level is not supported. found: $unsupportedIsolationLevel") {



}
