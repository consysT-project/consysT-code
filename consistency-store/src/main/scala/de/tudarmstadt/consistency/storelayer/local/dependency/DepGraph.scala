package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution.SessionService
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
trait DepGraph[Id, Key, Data, Txid] {

	protected val store : SessionService[Id, Txid, Key, Data, _, _, _]
	import store._

	private case class OpInfo(
		/*non-modifiable*/
    key : Key,
	  data : Data,
	  tx : Option[Txid],
    /*modifiable*/
		var local : Boolean = true,
//		var unresolvedDependencies : Option[Set[Id]] = None //unresolved dependencies of this Op, or None if the dependencies have not been checked yet
  )

	private val dependencyGraph : Graph[OpRef, DiEdge] = Graph.empty

	private val operations : mutable.Map[Id, OpInfo] = new mutable.HashMap

	private val transactions : mutable.MultiMap[Txid, OpRef] =
		new mutable.HashMap[Txid, mutable.Set[OpRef]] with mutable.MultiMap[Txid, OpRef]


	/**
		* Adds a new operation to this dependency graph.
		*
		* @param id the id of the operation
		* @param key the key of the operation
		* @param data the data of the operation
		* @param tx the transaction id if the operation is part of a transaction
		* @param deps the dependencies die other operations
		* @param local true, if the operation should be flagged as a local operation (i.e. if it is not part of the distributed data store and only available locally)
		*/
	def addOp(id : Id, key : Key, data : Data, tx : Option[Txid] = None, deps : Iterable[OpRef] = Iterable.empty, local : Boolean = true) : Unit = {
		/*add operation to operations*/
		operations(id) = OpInfo(key, data, tx, local)

		/*add an entry to the transaction if there is one*/
		val ref = OpRef(id, key)
		tx.foreach(txid => transactions.addBinding(txid, ref))

		/*add operation node to dependency graph*/
		dependencyGraph.add(OpRef(id, key))

		/*add all dependencies to the graph*/
		deps.foreach(dep => dependencyGraph.add(dep ~> ref))

		unresolveOp(id)
	}

	/**
		* Removes an operation from this dependency graph.
		*
		* @param id the id of the operation that is removed
		* @return the operation that was removed, or None if no operation with the id was known.
		*/
	def removeOp(id : Id) : Option[Op[Id, Key, Data]] = {
		/*unresolve all nodes where the node is a successor, has to be done before op is removed from operations*/
		unresolveOp(id)

		operations.remove(id) match { /*remove operation from operations, and check whether it existed*/
			case None =>
				//TODO: Remove this assert
				assert(false, s"operation with id $id does not exist")
				None
			case Some(opInfo) =>
				/*remove op from the transaction*/
				opInfo.tx.foreach(txid => transactions.removeBinding(txid, OpRef(id, opInfo.key)))

				/*do not remove any dependencies with the node. The dependencies still remain!*/
				/*return the removed node*/
				Some(Op(id, opInfo.key, opInfo.data))
		}
	}

	/**
		* Adds a new dependency to a transaction.
		*
		* @param txid the transaction that is appended
		* @param id the id of the operation that is added
		*/
	def addOpToTx(txid : Txid, id : OpRef*) : Unit = transactions.get(txid) match {
		case None =>
			val set = new mutable.HashSet[OpRef]()
			set ++= id
			transactions(txid) = set
		case Some(set) =>
			set ++= id
			set.foreach(e => unresolveOp(e.id))
	}


	def removeTx(txid : Txid) : Unit = transactions.get(txid) match {
		case None =>
			assert(false, s"transaction does not exist: $txid")
		case Some(deps) =>
			deps.foreach(dep => removeOp(dep.id))
			transactions.remove(txid)
	}

	def unresolvedDependencies(id : Id) : Set[Id] = {


		def unresolvedDependencies(id : Id, alreadyVisited : Set[Id]) : Set[Id] =	{
			operations.get(id) match {
				case None => Set(id) //id is unresolved itself

//				case Some(OpInfo(_, _, _, _)) => x //the operation id has been resolved already

				case Some(opInfo) if alreadyVisited.contains(id) => //in this case we have visited id, and did not resolve it.
					Set()

				case Some(opInfo) =>
					val predecessorsInGraph : Set[OpRef] = dependencyGraph.get(OpRef(id, opInfo.key)).diPredecessors.map(_.value)
					val unresolvedPreds = predecessorsInGraph.flatMap(pred => if (pred != id) unresolvedDependencies(pred.id, alreadyVisited + id) else Set.empty[Id])

					val dependenciesInTx : Set[OpRef] = opInfo.tx.map(txid => transactions(txid).toSet).getOrElse(Set.empty)
					val unresolvedTx = dependenciesInTx.flatMap(pred => if (pred != id) unresolvedDependencies(pred.id, alreadyVisited + id) else Set.empty[Id])

					val unresolved = unresolvedPreds ++ unresolvedTx

					unresolved
			}
		}

		unresolvedDependencies(id, Set.empty)
	}


	def getDependencies(ref : OpRef) : Set[OpRef] =
		dependencyGraph.get(ref).diPredecessors.map(_.value)


	def getOp(id : Id) : Op[Id, Key, Data] = {
		val opInfo = operations(id)
		Op(id, opInfo.key, opInfo.data)
	}


	/*
	Private helper methods
	*/
	private def unresolveOp(id : Id) : Unit = {}
//		operations.get(id) match {
//		case Some(opInfo@OpInfo(_, _, _, _, Some(_))) =>
//			opInfo.unresolvedDependencies = None
//			dependencyGraph.get(id).diSuccessors.foreach(node => unresolveOp(node.value))
//			opInfo.tx.foreach(txid => transactions(txid).foreach(txdep => unresolveOp(txdep)))
//		case _ => /*Nothing has to be done*/
//	}
}


object DepGraph {
	case class Op[Id, Key, Data](id : Id, key : Key, data : Data)


	private class TransactionMap[Id, Txid] {

		private val transactions : mutable.Map[Txid, Set[Id]] = new mutable.HashMap


	}
}
