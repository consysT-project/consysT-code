package de.tudarmstadt.consistency.store.shim

import scala.collection.mutable
import Event._
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/




//	sealed trait ReadResult[Id, Key, Data]
//	/*Some data has been successfully found and resolved (= all dependencies have been satisfied). It also returns the latest known value, as well as all unresolved dependencies for the latest value.*/
//	case class Resolved[Id, Key, Data](data : Update[Id, Key, Data], latest : Update[Id, Key, Data], unresolved: Set[EventRef[Id, Key]])  extends ReadResult[Id, Key, Data]
//	/*Data has been found but there are still some unresolved dependencies */
//	case class Unresolved[Id, Key, Data](data : Update[Id, Key, Data], unresolved : Set[EventRef[Id, Key]])  extends ReadResult[Id, Key, Data]
//	/*The key has not been found.*/
//	case class NotFound[Id, Key, Data]() extends ReadResult[Id, Key, Data]


//	case class ReadResult[Id, Key, Data](node : Option[Update[Id, Key, Data]], found : Boolean, unresolved : Set[EventRef[Id, Key]]) {
//		def getId : Option[Id] = node.map(n => n.getId)
//		def isFound : Boolean = found
//	}



class SessionOrder[Id : Ordering, Key, Data] {

	private type Node = Event[Id, Key, Data]

	//The latest node that has been created in this transaction
	private var sessionPointer : Option[UpdateRef[Id, Key]] = None
	//stores the session pointer before a transaction as a fallback in case the tx gets aborted.
	private var sessionPointerBeforeTx : Option[UpdateRef[Id, Key]] = None

	//The reads that occurred since the last node has been added
	private var readDependencies : Set[UpdateRef[Id, Key]] = Set.empty

	//The transaction id of the current transaction
	private var transactionPointer : Option[TxRef[Id]] = None
	//The ids of all updates that happened during this transaction
	private var transactionDependencies : Set[UpdateRef[Id, Key]] = Set.empty


	private [shim] val graph : DependencyGraph[Id, Key, Data] = new DependencyGraph()


	def addUpdate(id : Id, key : Key, data : Data): Unit = {
		val upd = graph.addUpdate(id, key, data, transactionPointer, getNextDependencies)

		val updRef = upd.toRef

		sessionPointer = Some(updRef)
		readDependencies = Set.empty

		if (transactionPointer.isDefined)
			transactionDependencies += updRef
	}

	def addRead(ref : UpdateRef[Id, Key]): Unit = {
		readDependencies = readDependencies + ref
	}

	def addRead(id : Id, key : Key) : Unit = {
		addRead(UpdateRef(id, key))
	}


	def getNextDependencies : Set[UpdateRef[Id, Key]] = {
		readDependencies ++ sessionPointer
	}

	//You need to manually add a read with addRead if this read should be visible as a dependency
	def read(key : Key) : Resolved[Update[Id, Key, Data], EventRef[Id, Key]] =
		graph.read(key, transactionPointer)


	def startTransaction(id : Id): Unit = {
		assert(transactionPointer.isEmpty)

		sessionPointerBeforeTx = sessionPointer
		transactionPointer = Some(TxRef(id))
		transactionDependencies = Set.empty
	}

	def commitTransaction(): Unit = transactionPointer match {
		case None => assert(assertion = false, "cannot commit a transaction that has never started")
		case Some(txRef) =>
			graph.addTx(txRef.id, transactionDependencies)
			transactionDependencies = Set.empty
			transactionPointer = None
	}

	def abortTransaction() : Unit = transactionPointer match {
		case None => assert(assertion = false, "cannot abort a transaction that has never started")
		case Some(id) =>
			transactionDependencies.foreach(ref => graph.remove(ref.id))
			transactionDependencies = Set.empty
			transactionPointer = None
			//Reset session pointer to "before the transaction"
			sessionPointer = sessionPointerBeforeTx
	}

	private [shim] def addRaw(update : Update[Id, Key, Data]) : Unit = {
		graph.addUpdate(update)
	}

	private [shim] def addRaw(tx : Tx[Id, Key, Data]) : Unit = {
		graph.addTx(tx)
	}


	override def toString : String = {
		graph.toString
	}

}

