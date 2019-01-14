package de.tudarmstadt.consistency.storelayer.local.dependency

import de.tudarmstadt.consistency.storelayer.distribution.SessionService
import de.tudarmstadt.consistency.storelayer.local.dependency


/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait Session[Id, Key, Data, Txid] {

	protected val store : SessionService[Id, Txid, Key, Data, _, _, _]
	import store._

	//The latest node that has been created in this transaction
	private var sessionPointer : Option[OpRef] = None

	//The reads that occurred since the last node has been added
	private var readDependencies : Set[OpRef] = Set.empty

	private[local] val graph : DepGraph[Id, Key, Data, Txid] = new DepGraph[Id, Key, Data, Txid] {
		override val store : SessionService[Id, Txid, Key, Data, _, _, _] = store
	}

	//the current state of the session
	private var state : SessionState = SessionState.Idle



	def lockUpdate(id : Id, key : Key, data : Data) : OpNode = synchronized {
		state.lockUpdate(id, key, data)
	}

	def releaseUpdate() : Unit = synchronized {
		state.releaseUpdate()
	}

	def confirmUpdate() : Unit = synchronized {
		state.confirmUpdate()
	}

	def addUpdate(id : Id, key : Key, data : Data) : OpNode = synchronized {
		val upd = lockUpdate(id, key, data)
		confirmUpdate()
		upd
	}


	def addRead(ref : OpRef): Unit = synchronized {
		readDependencies = readDependencies + ref
	}


	def getNextDependencies : Set[OpRef] = synchronized {
		readDependencies ++ sessionPointer
	}

	def getCurrentTxid : Option[Txid] = state match {
		case s : SessionStateInTx => Some(s.getTxid)
		case _ => None
	}


	//You need to manually add a read with addRead if this read should be visible as a dependency
//	def resolve(key : Key) : Resolved[Update[Id, Key, Data], EventRef[Id, Key]] = state match {
//		case s : SessionStateInTx => graph.resolve(key, Some(s.getTxid))
//		case _ => graph.resolve(key)
//	}



	def startTransaction(id : Txid): Unit = synchronized {
		state.startTransaction(id)
	}

	def lockTransaction() :  TxNode = synchronized {
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


	override def toString : String = {
		graph.toString
	}


	trait SessionState {
		def lockUpdate(id : Id, key : Key, data : Data) : OpNode =
			throw new IllegalStateException("cannot lock update in this state")

		def releaseUpdate() : Unit =
			throw new IllegalStateException("cannot release update in this state")
		def confirmUpdate() : Unit =
			throw new IllegalStateException("cannot confirm update in this state")

		def startTransaction(txid : Txid): Unit =
			throw new IllegalStateException("cannot start transaction in this state")

		def lockTransaction() : TxNode =
			throw new IllegalStateException("cannot lock transaction in this state")

		def commitTransaction() : Unit =
			throw new IllegalStateException("cannot commit transaction in this state")
		def abortTransaction() : Unit =
			throw new IllegalStateException("cannot abort transaction in this state")
	}

	trait SessionStateInTx extends SessionState {
		def getTxid : Txid
	}

	object SessionState {

		object Idle extends SessionState {
			override def lockUpdate(id : Id, key : Key, data : Data) : OpNode = {
				val node = OpNode(id, key, data, None, getNextDependencies)
				state = LockedUpdate(node)
				node
			}

			override def startTransaction(txid : Txid): Unit = {
				state = StartedTransaction(txid, sessionPointer)
			}
		}


		case class LockedUpdate(node : OpNode) extends SessionState {
			override def releaseUpdate() : Unit = {
				state = Idle
			}

			override def confirmUpdate() : Unit = {
				import node._
				graph.addOp(id, key, data, txid, dependencies)

				sessionPointer = Some(id)
				readDependencies = Set.empty

				state = Idle
			}
		}


		case class StartedTransaction(txid : Txid, sessionPointerBeforeTx : Option[OpRef]) extends SessionStateInTx {

			//The ids of all updates that happen during this transaction
			var transactionDependencies : Set[OpRef] = Set.empty

			override def lockUpdate(id : Id, key : Key, data : Data) : OpNode = {
				val node = OpNode(id, key, data, Some(TxRef(txid)), getNextDependencies)
				state = LockedUpdateInTx(this, node)
				node
			}

			override def lockTransaction() :  TxNode = {
				val tx = TxNode(txid, transactionDependencies)
				state = LockedTransaction(this, tx)
				tx
			}

			override def getTxid : Txid = txid
		}


		case class LockedUpdateInTx(txState : StartedTransaction, node : OpNode) extends SessionStateInTx {

			override def releaseUpdate() : Unit = {
				state = txState
			}

			override def confirmUpdate() : Unit = {
				graph.addOp(node.id, node.key, node.data, node.txid.map(txref => txref.txid), node.dependencies)

				sessionPointer = Some(node.id)
				readDependencies = Set.empty
				txState.transactionDependencies += node.id

				state = txState
			}

			override def getTxid : Txid = txState.getTxid
		}


		case class LockedTransaction(txState : StartedTransaction, tx : TxNode) extends SessionStateInTx {
			override def commitTransaction() : Unit = {
				txState.transactionDependencies = Set.empty
			//	graph.addLocalTx(tx)
				state = Idle
			}

			override def abortTransaction() : Unit = {
				txState.transactionDependencies.foreach(id => graph.removeOp(id))
				txState.transactionDependencies = Set.empty
				//Reset session pointer to "before the transaction"
				sessionPointer = txState.sessionPointerBeforeTx

				state = Idle
			}

			override def getTxid : Txid = txState.getTxid
		}
	}



}

