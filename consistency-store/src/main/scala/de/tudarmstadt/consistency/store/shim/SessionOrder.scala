package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store.shim.Event._
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

	//The reads that occurred since the last node has been added
	private var readDependencies : Set[UpdateRef[Id, Key]] = Set.empty



	private var state : SessionState = SessionState.Idle


	private [shim] val graph : DependencyGraph[Id, Key, Data] = new DependencyGraph()


	def lockUpdate(id : Id, key : Key, data : Data) : Update[Id, Key, Data] = synchronized {
		state.lockUpdate(id, key, data)
	}

	def releaseUpdate() : Unit = synchronized {
		state.releaseUpdate()
	}

	def confirmUpdate() : Unit = synchronized {
		state.confirmUpdate()
	}

	def addUpdate(id : Id, key : Key, data : Data) : Update[Id, Key, Data] = synchronized {
		val upd = lockUpdate(id, key, data)
		confirmUpdate()
		upd
	}


	def addRead(ref : UpdateRef[Id, Key]): Unit = synchronized {
		readDependencies = readDependencies + ref
	}

	def addRead(id : Id, key : Key) : Unit = {
		addRead(UpdateRef(id, key))
	}


	def getNextDependencies : Set[UpdateRef[Id, Key]] = synchronized {
		readDependencies ++ sessionPointer
	}

	//You need to manually add a read with addRead if this read should be visible as a dependency
	def resolve(key : Key) : Resolved[Update[Id, Key, Data], EventRef[Id, Key]] = state match {
		case s : SessionStateInTx => graph.resolve(key, Some(s.getTxid))
		case _ => graph.resolve(key)
	}



	def startTransaction(id : Id): Unit = synchronized {
		state.startTransaction(id)
	}

	def lockTransaction() :  Tx[Id, Key, Data] = synchronized {
		state.lockTransaction()
	}

	def commitTransaction(): Unit = synchronized {
		state.commitTransaction()
	}

	def abortTransaction() : Unit = synchronized {
		state.abortTransaction()
	}

	def abortTransactionIfStarted() : Unit = synchronized {
		state match {
			case _ : SessionState.LockedTransaction => state.abortTransaction()
			case _ : SessionState.StartedTransaction =>
				state.lockTransaction()
				state.abortTransaction()
		}
	}

	def lockAndCommitTransaction() : Unit = synchronized {
		lockTransaction()
		commitTransaction()
	}

	def lockAndAbortTransaction() : Unit = synchronized {
		lockTransaction()
		abortTransaction()
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


	trait SessionState {


		def lockUpdate(id : Id, key : Key, data : Data) : Update[Id, Key, Data] =
			throw new IllegalStateException("cannot lock update in this state")

		def releaseUpdate() : Unit =
			throw new IllegalStateException("cannot release update in this state")
		def confirmUpdate() : Unit =
			throw new IllegalStateException("cannot confirm update in this state")

		def startTransaction(id : Id): Unit =
			throw new IllegalStateException("cannot start transaction in this state")

		def lockTransaction() :  Tx[Id, Key, Data] =
			throw new IllegalStateException("cannot lock transaction in this state")

		def commitTransaction() : Unit =
			throw new IllegalStateException("cannot commit transaction in this state")
		def abortTransaction() : Unit =
			throw new IllegalStateException("cannot abort transaction in this state")
	}

	trait SessionStateInTx extends SessionState {
		def getTxid : TxRef[Id]
	}

	object SessionState {

		object Idle extends SessionState {

			override def lockUpdate(id : Id, key : Key, data : Data) : Update[Id, Key, Data] = {
				val upd = Update(id, key, data, None, getNextDependencies)
				state = LockedUpdate(upd)
				upd
			}

			override def startTransaction(id : Id): Unit = {
				val txRef = TxRef(id)
				state = StartedTransaction(txRef, sessionPointer)
			}
		}


		case class LockedUpdate(upd : Update[Id, Key, Data]) extends SessionState {

			override def releaseUpdate() : Unit = {
				state = Idle
			}

			override def confirmUpdate() : Unit = {
				graph.addUpdate(upd)

				sessionPointer = Some(upd.toRef)
				readDependencies = Set.empty

				state = Idle
			}
		}


		case class StartedTransaction(txRef : TxRef[Id], sessionPointerBeforeTx : Option[UpdateRef[Id, Key]]) extends SessionStateInTx {

			//The ids of all updates that happen during this transaction
			var transactionDependencies : Set[UpdateRef[Id, Key]] = Set.empty

			override def lockUpdate(id : Id, key : Key, data : Data) : Update[Id, Key, Data] = {
				val upd = Update(id, key, data, Some(txRef), getNextDependencies)
				state = LockedUpdateInTx(this, upd)
				upd
			}

			override def lockTransaction() :  Tx[Id, Key, Data] = {
				val tx : Tx[Id, Key, Data] = Tx(txRef.id, transactionDependencies)
				state = LockedTransaction(this, tx)
				tx
			}

			override def getTxid : TxRef[Id] = txRef
		}


		case class LockedUpdateInTx(txState : StartedTransaction, upd : Update[Id, Key, Data]) extends SessionStateInTx {

			override def releaseUpdate() : Unit = {
				state = txState
			}

			override def confirmUpdate() : Unit = {
				graph.addUpdate(upd)

				val updRef = upd.toRef
				sessionPointer = Some(updRef)
				readDependencies = Set.empty
				txState.transactionDependencies += updRef

				state = txState
			}

			override def getTxid : TxRef[Id] = txState.getTxid
		}


		case class LockedTransaction(txState : StartedTransaction, tx : Tx[Id, Key, Data]) extends SessionStateInTx {
			override def commitTransaction() : Unit = {
				graph.addTx(tx)
				txState.transactionDependencies = Set.empty

				state = Idle
			}

			override def abortTransaction() : Unit = {
				txState.transactionDependencies.foreach(ref => graph.remove(ref.id))
				//Reset session pointer to "before the transaction"
				sessionPointer = txState.sessionPointerBeforeTx

				state = Idle
			}

			override def getTxid : TxRef[Id] = txState.getTxid
		}
	}



}

