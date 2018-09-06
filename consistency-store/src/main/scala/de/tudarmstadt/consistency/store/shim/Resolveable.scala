package de.tudarmstadt.consistency.store.shim

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
trait Resolveable {
	private val resolvedDependencies : Array[Boolean] = Array(false)
	def isResolved : Boolean = resolvedDependencies(0)
	def setResolved(): Unit =	resolvedDependencies(0) = true
}
