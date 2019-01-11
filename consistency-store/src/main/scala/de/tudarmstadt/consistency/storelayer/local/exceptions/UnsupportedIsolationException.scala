package de.tudarmstadt.consistency.storelayer.local.exceptions

/**
	* Created on 11.01.19.
	*
	* @author Mirko Köhler
	*/
class UnsupportedIsolationException(isolation : Any)
	extends RuntimeException(s"unsupported isolation level: $isolation")