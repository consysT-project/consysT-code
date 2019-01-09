package de.tudarmstadt.consistency.storelayer.local.dependency

import scalax.collection.mutable.Graph
import scalax.collection.GraphPredef._, scalax.collection.GraphEdge._


import scala.collection.mutable

/**
	* Created on 08.01.19.
	*
	* @author Mirko Köhler
	*/
class DependencyGraph[Id, Key, Data, Txid] {
	/* inner data definitions */
	//operations
	private case class Op(key : Key, data : Data, txid : Option[Txid])

	/*
	operations are divided between global and local operations. Global operations
	have been observed in the global datastore, whereas local operations have been
	created by the local process. When a local operation is added to the datastore

	 */
	//mutable hashmap for all operations that are consistent with the underlying datastore
	private val globalOperations : mutable.Map[Id, Op] = mutable.Map.empty
	//mutable hashmap for operations that are only available locally at the host
	private val localOperations : mutable.Map[Id, Op] = mutable.Map.empty

	//mutable map for tracking transaction dependencies
	private val transactions : mutable.MultiMap[Txid, Id] = new mutable.HashMap[Txid, mutable.Set[Id]]() with mutable.MultiMap[Txid, Id]

	//mutable graph for dependencies between operations
	private val dependencyGraph : Graph[Id, DiEdge] = Graph.empty


	final def addGlobalOp(node : OpNode[Id, Key, Data, Txid]) : Unit = {
		import node._
		addGlobalOp(id, key, data, txid, dependencies)
	}

	def addGlobalOp(id : Id, key : Key, data : Data, txid : Option[Txid], dependencies : Set[Id]) : Unit = {
		assert(!globalOperations.contains(id), "the id was already in use")
		assert(!localOperations.contains(id), "the id was already in use locally")

		//Update the operations map
		globalOperations += ((id, Op(key, data, txid)))

		//Update the dependency graph
		dependencyGraph += id
		dependencies.foreach { dep =>
			dependencyGraph += (dep ~> id)
		}
	}

	final def addLocalOp(node : OpNode[Id, Key, Data, Txid]) : Unit = {
		import node._
		addLocalOp(id, key, data, txid, dependencies)
	}

	def addLocalOp(id : Id, key : Key, data : Data, txid : Option[Txid], dependencies : Set[Id]) : Unit = {
		assert(!globalOperations.contains(id), "the id was already in use")
		assert(!localOperations.contains(id), "the id was already in use locally")

		//Update the operations map
		localOperations += ((id, Op(key, data, txid)))

		//Update the dependency graph
		dependencyGraph += id
		dependencies.foreach { dep =>
			dependencyGraph += (dep ~> id)
		}
	}

	final def addGlobalTx(node : TxNode[Id, Txid]) : Unit = {
		import node._
		addGlobalTx(txid, dependencies)
	}

	def addGlobalTx(id : Txid, dependencies : Set[Id]) : Unit = {
		assert(!transactions.contains(id), "the txid was already in use")

		dependencies.foreach { dep =>
			transactions.addBinding(id, dep)
		}
	}

	final def addLocalTx(node : TxNode[Id, Txid]) : Unit = {
		import node._
		addLocalTx(txid, dependencies)
	}

	def addLocalTx(id : Txid, dependencies : Set[Id]) : Unit = {
		//TODO: implement local tx
		addGlobalTx(id, dependencies)
	}


	def removeLocalOp(id : Id) : Unit = {
		assert(localOperations.contains(id), s"cannot remove operation that is not contained in graph")

		localOperations -= id
		dependencyGraph -= id
	}

	def changeToGlobal(id : Id) : Unit = {
		localOperations.remove(id) match {
			case None => assert(false, s"can only make a local operation global")
			case Some(op) =>
				assert(!globalOperations.contains(id), s"operation already exists")
				globalOperations += ((id, op))
		}
	}


	def dependenciesSatisfiedGlobally(id : Id) : Boolean = globalOperations.get(id) match {
		case None => false
		case Some(Op(key, data, txid)) =>
			assert(dependencyGraph.contains(id), s"the dependency graph is inconsistent with the operations table")
			lazy val deps : Boolean = dependencyGraph.get(id).diPredecessors.forall(pred => dependenciesSatisfiedGlobally(pred.value))

			txid match {
				case None => deps
				case Some(tx) => transactions.get(tx) match {
					case None => false
					case Some(txDeps) => txDeps.forall(dep => dependenciesSatisfiedGlobally(dep)) && deps
				}
			}
	}


	def unsatisfiedGlobalDependencies(id : Id) : Set[Id] = globalOperations.get(id) match {
		case None => Set(id)
		case Some(Op(key, data, txid)) =>
			assert(dependencyGraph.contains(id), s"the dependency graph is inconsistent with the operations table")
			val deps = dependencyGraph.get(id).diPredecessors.flatMap(pred => unsatisfiedGlobalDependencies(pred.value))

			txid match {
				case None => deps
				case Some(tx) => transactions.get(tx) match {
					case None => deps + id
					case Some(txDeps) => txDeps.toSet.flatMap(dep => unsatisfiedGlobalDependencies(dep)) ++ deps
				}
			}
	}
}
