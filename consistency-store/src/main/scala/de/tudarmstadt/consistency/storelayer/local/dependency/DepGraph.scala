package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution
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

	private trait NodeInfo {
		var local : Boolean
	}

	private case class OpInfo(
		/*non-modifiable*/
    key : Key,
	  data : Data,
    /*modifiable*/
		override var local : Boolean = true
//		var unresolvedDependencies : Boolean = false //true, if all depedencies of this op have been resolved
  ) extends NodeInfo

	private case class TxInfo(
		override var local : Boolean = true
	) extends NodeInfo

	/* ### Data structures ### */
	/**
		* Graph of dependencies between operations. The graph stores identifiers
		* to operations (as OpRef). These identifiers are looked up in the
		* operations map.
		* OpRefs in the graph can be unavailable in the operations map. This means
		* that the operation has not been resolved from the underlying store
		* but is known to the graph (e.g. through a dependency of another node).
		*/
	private val dependencyGraph : Graph[Ref, DiEdge] = Graph.empty

	/**
		* Maps ids to their respective operations. Ids that can not be resolved
		* in the map (i.e. there is no entry), have not been resolved in the
		* underlying graph, or simply do not exist (although this can not be said for sure).
		*/
	private val operations : mutable.Map[Id, OpInfo] = new mutable.HashMap

	/**
		* Maps transaction ids to all operations that are contained in that transaction.
		* This map is used to resolve transaction dependencies. An entry in this map
		* can be seen as a dependency of all nodes in the tx to each other.
		*/
	private val transactions : mutable.Map[Txid, TxInfo] = new mutable.HashMap

	/**
		* Stores the "newest" operation ids for each key. "New" here means that it stores
		* all operations that no other operation of the same key has a transitive dependency
		* to that dependency. The concrete conflict resolution algorithm is not
		* defined here.
		*/
//	private val keys : mutable.MultiMap[Key, Id] =
//		new mutable.HashMap[Key, Id] with mutable.MultiMap[Key, Id]


	/* ### Operations ### */

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
		val newRef = store.ref(id, key)

		/*add operation to operations*/
		operations(id) = OpInfo(key, data, local)

		/*add an entry to the transaction if there is one*/
		tx.foreach { txid => addOpsToTx(txid, newRef) }

		/*add operation node to dependency graph*/
		dependencyGraph.add(newRef)
		/*add all dependencies to the graph*/
		deps.foreach(dep => {
			dependencyGraph.add(dep ~> newRef)
		})

		/*update keys*/
//		updatePointersForKey(newRef)
	}


//	private def updatePointersForKey(newRef : OpRef) : Unit = {
//		//The key to be checked
//		val key = newRef.key
//		//the id of the new update
//		val newId = newRef.id
//
//		//obtains the node of the new ref from the graph
//		val newNode = dependencyGraph.get(newRef)
//		//obtains the current node ids for the key that is checked
//		val pointers = keys.get(key).toSet.flatten
//
//
//		//Check whether to delete entries in the keys map
//		pointers.foreach { id =>
//			val node = dependencyGraph.get(ref(id, key))
//
//			val maybePath = node
//				.withSubgraph(nodes = nodeT => operations.contains(nodeT.id)) //
//				.pathTo(newNode)
//
//			maybePath match {
//				case None => //if there is no path between the previousNode and the currentNode
//
//				case Some(path) => //if there is a path between the old node and the new node, then it is safe to delete
//					keys.removeBinding(key, id)
//			}
//		}
//
//		//Check whether to add the new node to the keys table.
//		pointers.foreach { id =>
//			val previousNode = dependencyGraph.get(ref(id, key))
//
//			val maybePath = previousNode
//				.withSubgraph(nodes = nodeT => operations.contains(nodeT.id)) //
//				.pathTo(newNode)
//
//			maybePath match {
//				case None => //if there is no path between the previousNode and the currentNode
//
//				case Some(path) => //if there is a path between the old node and the new node, then it is safe to delete
//					keys.removeBinding(key, id)
//			}
//		}
//	}


	def +=(id : Id, key : Key, data : Data, tx : Option[Txid], deps : OpRef*) : Unit = {
		addOp(id, key, data, tx, deps)
	}

	def +=(id : Id, key : Key, data : Data, deps : OpRef*) : Unit = {
		addOp(id, key, data, deps = deps)
	}

	/**
		* Removes an operation from this dependency graph.
		*
		* @param id the id of the operation that is removed
		* @return the operation that was removed, or None if no operation with the id was known.
		*/
	def removeOp(id : Id) : Option[Op[Id, Key, Data]] = {
		/*unresolve all nodes where the node is a successor, has to be done before op is removed from operations*/
		operations.remove(id).map(opInfo => Op(id, opInfo.key, opInfo.data))
	}

	/**
		* Adds a new dependency to a transaction.
		*
		* @param txid the transaction that is appended
		* @param ops the id of the operation that is added
		*/
	def addOpsToTx(txid : Txid, ops : OpRef*) : Unit = {
		val txRef = ref(txid)

		//automatically adds a node if one of the edge endpoints does not exist
		ops.foreach { opRef =>
			dependencyGraph.add(opRef ~> txRef)
			dependencyGraph.add(txRef ~> opRef)
		}
	}

	/**
		* Adds a new transaction to the dependency graph.
		*
		* @param txid the identifier of the transaction.
		*/
	def addTx(txid : Txid) : Unit = {
		transactions(txid) = TxInfo()
	}

	/**
		* Removes a transaction from the dependency graph. Does not remove
		* operations in the transaction.
		*
		* @param txid id of the removed transaction
		*/
	def removeTx(txid : Txid) : Unit = {
		transactions.remove(txid)
	}

	/**
		* Removes a transaction and all operations in that transaction.
		*/
	def purgeTx(txid : Txid) : Unit = {
		transactions.remove(txid)

		val txNode = getNode(txid)

		txNode.diSuccessors.foreach { node => node.value match {
				case distribution.OpRef(id : Id, _) => operations.remove(id)
				case _ => sys.error(s"dependency of tx is expected to be opref")
			}
		}
	}

	/**
		* Computes one (transitive) reference of an operation
		* that is not resolved.
		*
		* @param ref the reference to the operation.
		* @return Some reference that is not resolved or None if all references are resolved.
		*/
	def unresolvedDependencies(ref : Ref) : Option[Ref] = {

//		def unresolvedDependencies(r : Ref, visitedOps : Set[Id], visitedTxs : Set[Txid]) : Set[Ref] =	getInfo(r) match {
//			case None => Set(r) //id is unresolved itself
//
//			case Some(distribution.OpRef(id : Id, _)) if visitedOps.contains(id) => //in this case we have visited id, and did not resolve it.
//				Set()
//
//			case Some(distribution.TxRef(txid : Txid)) if visitedTxs.contains(txid) => //in this case we have visited id, and did not resolve it.
//				Set()
//
//			case Some(ref : Ref) =>
//
//
//
//
//					diPredecessors.map(_.value)
//
//				val unresolvedPreds = predecessorsInGraph.flatMap { predNode =>
//					pred => if (pred != id) unresolvedDependencies(pred.id, alreadyVisited + id) else Set.empty[Id]
//				}
//
//				val dependenciesInTx : Set[OpRef] = opInfo.tx.map(txid => transactions(txid).toSet).getOrElse(Set.empty)
//				val unresolvedTx = dependenciesInTx.flatMap(pred => if (pred != id) unresolvedDependencies(pred.id, alreadyVisited + id) else Set.empty[Id])
//
//				val unresolved = unresolvedPreds ++ unresolvedTx
//
//				unresolved
//		}

		val predecessorsInGraph : Option[dependencyGraph.NodeT] = getNode(ref).findPredecessor(node => node.value match {
			case distribution.OpRef(id : Id, _) => operations.contains(id)
			case distribution.TxRef(txid : Txid) => transactions.contains(txid)
		})

		predecessorsInGraph.map(node => node.value)
	}


	def getDependencies(ref : Ref) : Set[Ref] = {
		require(getInfo(ref).isDefined)
		dependencyGraph.get(ref).diPredecessors.map(_.value)
	}

	def getDependencies(id : Id, key : Key) : Set[Ref] =
		getDependencies(ref(id, key))

	def getDependencies(txid : Txid) : Set[Ref] = {
		getDependencies(ref(txid) : Ref)
	}


	def getOp(id : Id) : Option[Op[Id, Key, Data]] =
		operations.get(id).map(opInfo => Op(id, opInfo.key, opInfo.data))


	def apply(id : Id) : Op[Id, Key, Data] = getOp(id) match {
		case None => throw new NoSuchElementException(s"operation with id $id does not exist")
		case Some(op) => op
	}


//	def read(key : Key) : Set[Op[Id, Key, Data]] = {
//
//	}


	/*
	Private helper methods
	*/
	private def getOpInfo(id : Id) : Option[OpInfo] = operations.get(id)
	private def getTxInfo(txid : Txid) : Option[TxInfo] = transactions.get(txid)

	private def getInfo(ref : Ref) : Option[NodeInfo] = ref match {
		case distribution.OpRef(id, key) => operations.get(id)
		case distribution.TxRef(txid) => transactions.get(txid)
	}

	private def getNode(id : Id, key : Key) : dependencyGraph.NodeT =
		dependencyGraph.get(ref(id, key))
	private def getNode(txid : Txid) : dependencyGraph.NodeT =
		dependencyGraph.get(ref(txid))
	private def getNode(ref : Ref) : dependencyGraph.NodeT =
		dependencyGraph.get(ref)


}


object DepGraph {
	case class Op[Id, Key, Data](id : Id, key : Key, data : Data) extends Product3[Id, Key, Data] {
		@inline override final def _1 : Id = id
		@inline override final def _2 : Key = key
		@inline override final def _3 : Data = data
	}


	private class TransactionMap[Id, Txid] {

		private val transactions : mutable.Map[Txid, Set[Id]] = new mutable.HashMap


	}
}
