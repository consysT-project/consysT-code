package de.tudarmstadt.consistency.store.shim

import scala.collection.mutable

/**
	* Created on 09.10.18.
	*
	* @author Mirko Köhler
	*/
class TransactionDependencyGraph[Id, Key] {

	trait Ref {
		val id : Id
	}
	case class NodeRef(id : Id, key : Key) extends Ref


	case class Transaction(id : Id, nodes : mutable.Seq[Node])
	case class Node(id : Id, key : Key, dependencies : Set[NodeRef])






}
