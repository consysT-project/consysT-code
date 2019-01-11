package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.local.dependency.DepGraph.Op
import scalax.collection.mutable.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._

import scala.collection.mutable


/**
	* This is the implementation of a dependency graph between operations.
	* The graph consists of nodes (id, key, data) which are connected by
	* directed edges resembling their dependencies.
	*
	* Nodes are grouped in transactions, and can be local (= not in sync with
	* the distributed store).
	*
	* @author Mirko Köhler
	*/
class DepGraph[Id, Key, Data, Txid] {

	private case class OpInfo(
		/*non-modifiable*/
    key : Key,
	  data : Data,
	  tx : Option[Txid],
    /*modifiable*/
		var local : Boolean = true,
		var resolvedDependencies : Boolean = false
  )

	private val dependencyGraph : Graph[Id, DiEdge] = Graph.empty

	private val operations : mutable.Map[Id, OpInfo] = new mutable.HashMap

	private val transactions : mutable.MultiMap[Txid, Id] =
		new mutable.HashMap[Txid, mutable.Set[Id]] with mutable.MultiMap[Txid, Id]


	def addOp(id : Id, key : Key, data : Data, tx : Option[Txid] = None, deps : Iterable[Id], local : Boolean = true) : Unit = {
		/*add operation to operations*/
		operations.put(id, new OpInfo(key, data, tx, local))

		/*add an entry to the transaction if there is one*/
		tx.foreach(txid => transactions.addBinding(txid, id))

		/*add operation node to dependency graph*/
		dependencyGraph.add(id)

		/*add all dependencies to the graph*/
		deps.foreach(dep => dependencyGraph.add(dep ~> id))
	}

	def removeOp(id : Id) : Option[Op[Id, Key, Data]] = operations.remove(id) match { /*remove operation from operations, and check whether it existed*/
		case None =>
			//TODO: Remove this assert
			assert(false, s"operation with id $id does not exist")
			None
		case Some(opInfo) =>
			/*unresolve all nodes where the node is a successor*/
			unresolveOp(id)

			/*remove op from the transaction*/
			opInfo.tx.foreach(txid => transactions.removeBinding(txid, id))

			/*remove node from the dependency graph, also removes all adjacent edges*/
			dependencyGraph.remove(id)

			/*return the removed node*/
			Some(Op(id, opInfo.key, opInfo.data))
	}



	def removeTx(txid : Txid) : Unit = transactions.get(txid) match {
		case None =>
			assert(false, s"transaction does not exist: $txid")
		case Some(deps) =>
			deps.foreach(dep => removeOp(dep))
			transactions.remove(txid)
	}

	def unresolvedDependencies(id : Id) : Set[Id] = operations.get(id) match {
		case None => Set(id) //id is unresolved itself

		case Some(OpInfo(_, _, _, _, true)) => Set.empty //the operation id has been resolved already

		case Some(opInfo) =>
			val preds : Set[Id] = dependencyGraph.get(id).diPredecessors.map(_.value) ++
				opInfo.tx.map(txid => transactions(txid).toSet).getOrElse(Set.empty)

			val unresolved = preds.flatMap(id => unresolvedDependencies(id))

			if (unresolved.isEmpty) opInfo.resolvedDependencies = true

			unresolved
	}




	/*
	Private helper methods
	*/

	private def unresolveOp(id : Id) : Unit = operations.get(id) match {
		case Some(opInfo@OpInfo(_, _, _, _, true)) =>
			opInfo.resolvedDependencies = false
			dependencyGraph.get(id).diSuccessors.foreach(node => unresolveOp(node.value))
			opInfo.tx.foreach(txid => transactions(txid).foreach(txdep => unresolveOp(txdep)))
		case _ => /*Nothing has to be done*/

	}




}

object DepGraph {
	case class Op[Id, Key, Data](id : Id, key : Key, data : Data)


	private class TransactionMap[Id, Txid] {

		private val transactions : mutable.Map[Txid, Set[Id]] = new mutable.HashMap


	}
}
