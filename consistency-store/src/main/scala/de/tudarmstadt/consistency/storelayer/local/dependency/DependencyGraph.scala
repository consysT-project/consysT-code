package de.tudarmstadt.consistency.storelayer.local.dependency

import scalax.collection.GraphEdge.DiEdge
import scalax.collection.mutable.Graph

import scala.collection.mutable

/**
	* Created on 08.01.19.
	*
	* @author Mirko Köhler
	*/
class DependencyGraph {

	type Node

	val graph : Graph[Node, DiEdge] = Graph.empty

	val sessionPointers : mutable.Set[Node] = mutable.Set.empty

	val unconnectedNodes : mutable.Set[Node] = mutable.Set.empty

}
