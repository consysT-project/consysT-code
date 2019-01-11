package de.tudarmstadt.consistency.storelayer.local

import com.datastax.driver.core.exceptions.{NoHostAvailableException, QueryExecutionException}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.exceptions.{UnsupportedConsistencyLevelException, UnsupportedIsolationLevelException}
import de.tudarmstadt.consistency.store.cassandra.{CassandraReadParams, CassandraTxParams, CassandraWriteParams, SysnameCassandraStore}
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}
import de.tudarmstadt.consistency.store.shim.SessionOrder
import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.dependency.{DepGraph, Session}
import de.tudarmstadt.consistency.storelayer.local.protocols.SnapshotIsolatedTransactionProtocol
import de.tudarmstadt.consistency.utils.Log

import scala.collection.mutable

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait LocalLayer[Id, Key, Data, TxStatus, Isolation, Consistency] {

	protected val store : SessionService[Id, Key, Data, TxStatus, Isolation, Consistency]
		with IdService[Id]
		with DatastoreService[Id, Key, Data, TxStatus, Isolation, Consistency]

	import store._


	private val session : Session[Id, Key, Data, Id] = new Session[Id, Key, Data, Id] {}

	private var currentTransaction : Option[Transaction] = None



	/* writes and reads */
	final def write(consistency : Consistency, key : Key, data : Data) : Unit = currentTransaction match {
		case None => handleWrite(consistency, key, data)
		case Some(tx) => tx.handleWrite(consistency, key, data)
	}

	final def read(consistency : Consistency, key : Key) : Option[Data]  = currentTransaction match {
		case None => handleRead(consistency, key)
		case Some(tx) => tx.handleRead(consistency, key)
	}

	private[local] def handleWrite(consistency : Consistency, key : Key, data : Data) : Unit  =
		throw new UnsupportedConsistencyLevelException[Consistency](consistency)

	private[local] def handleRead(consistency : Consistency, key : Key) : Option[Data] =
		throw new UnsupportedConsistencyLevelException[Consistency](consistency)

	/* transactions */
	trait Transaction {

		private[local] def handleWrite(consistency : Consistency, key : Key, data : Data) : Unit =
			throw new UnsupportedConsistencyLevelException[Consistency](consistency)

		private[local] def handleRead(consistency : Consistency, key : Key) : Option[Data] =
			throw new UnsupportedConsistencyLevelException[Consistency](consistency)

		final def commit() : Unit = currentTransaction match {
			case None => throw new IllegalStateException("no transaction running.")
			case Some(tx) =>
				if(tx != this) {
					throw new IllegalStateException("can only commit transaction that is currently running")
				}
				handleCommit()
				session.lockAndCommitTransaction()
				currentTransaction = None
		}


		final def abort() : Unit = currentTransaction match {
			case None => throw new IllegalStateException("no transaction running.")
			case Some(tx) =>
				if(tx != this) {
					throw new IllegalStateException("can only abort transaction that is currently running")
				}
				handleAbort()
				session.lockAndAbortTransaction()
				currentTransaction = None
		}

		protected def handleCommit() : Unit =
			throw new UnsupportedOperationException

		protected def handleAbort() : Unit =
			throw new UnsupportedOperationException

	}

	final def startTransaction(isolation : Isolation) : Transaction = currentTransaction match {
		case None =>
			val txid = freshId()

			val tx = handleStartTransaction(isolation, txid)

			session.startTransaction(txid)
			currentTransaction = Some(tx)
			tx

		case Some(tx) =>
			throw new IllegalStateException(s"transaction already in process: $tx")
	}

	protected def handleStartTransaction(isolation : Isolation, txid : Id) : Transaction =
		throw new UnsupportedIsolationLevelException[Isolation](isolation)




}

object LocalLayer {

	trait SnapshotIsolatedTransactionsLayer[Id, Key, Data, TxStatus, Isolation, Consistency]
		extends LocalLayer[Id, Key, Data, TxStatus, Isolation, Consistency]
		with SnapshotIsolatedTransactionProtocol[Id, Key, Data, TxStatus, Isolation, Consistency] {

		override protected val store :  SessionService[Id, Key, Data, TxStatus, Isolation, Consistency]
			with IdService[Id]
			with DatastoreService[Id, Key, Data, TxStatus, Isolation, Consistency]
			with CoordinationService[Id, TxStatus, Isolation]
			with OptimisticLockService[Id, Key]
			with TxStatusBindings[TxStatus]
			with IsolationBindings[Isolation]

		import store._

		override protected def handleStartTransaction(isolation : Isolation, txid : Id) : Transaction =
			if (isolation == Isolation.SI) {
				new SnapshotIsolatedTransaction(txid)
			} else {
				super.handleStartTransaction(isolation, txid)
			}


		private class SnapshotIsolatedTransaction(val txid : Id) extends Transaction {

			private val writeBuffer : mutable.Buffer[DataWrite] = mutable.Buffer.empty



			override private[local] def handleWrite(consistency : Consistency, key : Key, data : Data) : Unit = {

			}

			override protected def handleCommit() : Unit = {
//				(id : Id, key : Key, data : Data, txid : Option[TxRef], dependencies : Set[OpRef], consistency : Consistency)
//
//				val txWrite = TxWrite(txid, )
//				commitWrites()

			}

		}

/*


		class SysnameShimSnapshotIsolatedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {

			//TODO: Snap shots are not created using the consistency level (e.g. what is a causal snapshot?)

			private val readCache : mutable.Map[Key, Option[Update[Id, Key, Data]]] = mutable.HashMap.empty

			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = Ids.freshId()
				val update = handleWrite(baseTx)(id, key, data, consistency)
				readCache.put(key, Some(update))
			}

			def read(key : Key, consistency : Consistency) : Read = readCache.get(key) match {
				//The key was not found -> read from the underlying store
				case None => handleRead(baseTx)(key, consistency) match {
					//The underlying store did not return a valid read
					case None =>
						readCache.put(key, None)
						return convertNone
					//The underlying did return something
					case Some(upd) =>
						readCache.put(key, Some(upd))
						return convertResult(upd)
				}

				//There was already an entry in the local cache
				case Some(maybeUpd) => maybeUpd match {
					//The cached value was none (i.e. the last read from that key returned none)
					case None =>
						return convertNone
					//There was some real value cached
					case Some(upd) =>
						return convertResult(upd)
				}
			}
		}
*/

	}

}
/*


	class SysnameShimSessionContext(val baseSession : BaseSessionContext) extends SessionContext {

		override type TxCtx = ShimTxContext
		type BaseTxContext = baseSession.TxContext

		private val sessionOrder : SessionOrder[Id, Key, Data] = new SessionOrder[Id, Key, Data]


		override def startTransaction[U](isolation : Isolation)(f : Transaction[U]) : Option[U] = isolation match {
				case IsolationLevels.NONE =>
					handleNoneIsolatedTransactions(f, isolation, baseTx => new SysnameShimNoneTxContext(baseTx))

				case IsolationLevels.RU =>
					handleIsolatedTransaction(f, isolation, baseTx => new SysnameShimReadUncommittedTxContext(baseTx))

				case IsolationLevels.RC =>
					handleIsolatedTransaction(f, isolation, baseTx => new SysnameShimReadCommittedTxContext(baseTx))

				case IsolationLevels.SI =>
					handleIsolatedTransaction(f, isolation, baseTx => new SysnameShimSnapshotIsolatedTxContext(baseTx))

				case l =>
					throw new UnsupportedIsolationLevelException(l)
			}


		private def handleNoneIsolatedTransactions[U](f : Transaction[U], isolation : Isolation, makeCtx : BaseTxContext => ShimTxContext) : Option[U] = {
			val txParams = CassandraTxParams[Id, Isolation](None, isolation)

			try {
				baseSession.startTransaction(txParams) { baseTx =>
					val tx = new SysnameShimNoneTxContext(baseTx)
					f(tx)
				} match {
					case None =>
						assert(assertion = false, "a 'none'-isolated transaction can not be aborted")
						None
					case opt@Some(_) =>
						opt
				}
			} catch {
				case e : NoHostAvailableException =>
					e.printStackTrace()
					sessionOrder.abortTransactionIfStarted()
					return None
				case e : QueryExecutionException =>
					//TODO: Differentiate between different errors here. What to do if the write was accepted partially?
					e.printStackTrace()
					sessionOrder.abortTransactionIfStarted()
					return None
			}
		}

		private def handleIsolatedTransaction[U](f : Transaction[U], isolation : Isolation, makeCtx : BaseTxContext => ShimTxContext) : Option[U] = {

			val txid = Ids.freshId()

			//Start the transaction in this session
			sessionOrder.startTransaction(txid)


			val txParams = CassandraTxParams(Some(txid), isolation)

			try {
				//Start a transaction in the base store
				baseSession.startTransaction(txParams) { baseTx =>
					val txContext = makeCtx(baseTx)
					val res = f(txContext) //execute the transaction as defined by the user

					//Lock the transaction and add the transaction record to the base store
					val tx = sessionOrder.lockTransaction()
					//TODO: Which consistency level do we use when writing the tx record.
					baseTx.writeTx(tx, CassandraWriteParams(ConsistencyLevels.CAUSAL))

					res
				} match {
					case None =>
						sessionOrder.abortTransactionIfStarted()
						return None
					case opt@Some(_) =>
						sessionOrder.commitTransaction()
						return opt
				}
			} catch {
				case e : NoHostAvailableException =>
					e.printStackTrace()
					sessionOrder.abortTransactionIfStarted()
					return None
				case e : QueryExecutionException =>
					//TODO: Differentiate between different errors here. What to do if the write was accepted partially?
					e.printStackTrace()
					sessionOrder.abortTransactionIfStarted()
					return None
			}
		}


		private def handleRead(baseTx : BaseTxContext)(key : Key, consistency : Consistency) : Option[Update[Id, Key, Data]] = consistency match {
			case ConsistencyLevels.CAUSAL => handleCausalRead(baseTx)(key)
			case ConsistencyLevels.WEAK => handleWeakRead(baseTx)(key)
			case ConsistencyLevels.LOCAL => handleLocalRead(baseTx)(key)
			case _ => throw new UnsupportedConsistencyLevelException(consistency)
		}


		private def handleLocalRead(baseTx : BaseTxContext)(key : Key) : Option[Update[Id, Key, Data]] = {

			sessionOrder.resolve(key) match {
				//If we got some value, just return the latest one (without checking any dependencies)
				case Found(_, latestUpdate, _) =>
					assert(latestUpdate.key == key, "the read update needs to have the same key as the key that was requested")
					sessionOrder.addRead(latestUpdate.toRef)
					return Some(latestUpdate)

				//If the key could not be found, then we can not read it
				case _ =>
					return None
			}
		}


		private def handleWeakRead(baseTx : BaseTxContext)(key : Key) : Option[Update[Id, Key, Data]] = {

			val updates = baseTx.read(key, CassandraReadParams(None, ConsistencyLevels.WEAK))
			addUpdates(updates)

			sessionOrder.resolve(key) match {
				//If we got some value, just return the latest one (without checking any dependencies)
				case Found(_, latestUpdate, _) =>
					assert(latestUpdate.key == key, "the read update needs to have the same key as the key that was requested")
					sessionOrder.addRead(latestUpdate.toRef)
					return Some(latestUpdate)

				//If the key could not be found, then we can not read it
				case _ =>
					return None
			}
		}

		private def handleCausalRead(baseTx : BaseTxContext)(key0 : Key) : Option[Update[Id, Key, Data]] = {

			//TODO: Check performance of causal reads
			/*
			A causal read retrieves all updates for the specified key, but for the dependencies
			it only retrieves a single id. Is it more performant to also retrieve all updates for that key?
			 */
			val updates = baseTx.read(key0, CassandraReadParams(None, ConsistencyLevels.CAUSAL))
			addUpdates(updates)

			def handleCausalReadRec(key : Key, alreadyTried : Set[Id]) : Option[Update[Id, Key, Data]] = sessionOrder.resolve(key) match {
				//If we read a resolved value and that value is already the latest, we can just return that value
				case Found(Some(resolvedUpdate), latestUpdate, _) if resolvedUpdate == latestUpdate =>
					assert(latestUpdate.key == key, "the read update needs to have the same key as the key that was requested")

					sessionOrder.addRead(resolvedUpdate.toRef)
					return Some(resolvedUpdate)
				//If we have a resolved value but there is a newer value that has not been resolved yet
				case Found(optionalUpdate, latestUpdate, unresolved) =>
					assert(latestUpdate.key == key, "the read update needs to have the same key as the key that was requested")

					//..., then try to resolve it
					val unresolvedSet : Set[Event[Id, Key, Data]]= unresolved.flatMap {
						case UpdateRef(refId, refKey) =>

							//if the key has already been updated in this run, then abort this read and return the version that could have been resolved
							if (alreadyTried.contains(refId)) {
								optionalUpdate.foreach(resolvedUpdate => sessionOrder.addRead(resolvedUpdate.toRef))
								return optionalUpdate
							}

							val rawRows = baseTx.read(refKey, CassandraReadParams(Some(refId), ConsistencyLevels.CAUSAL))
							addUpdates(rawRows)
							handleCausalReadRec(refKey, alreadyTried + refId)

						case TxRef(refId) =>

							if (alreadyTried.contains(refId)) {
							//	optionalUpdate.foreach(resolvedUpdate => sessionOrder.addRead(resolvedUpdate.toRef))
								return optionalUpdate
							}

							//TODO: How to add transaction reads? Do we even need to add them?
//							val rawRows = baseTx.read(Keys.TX_KEY, CassandraReadParams(Some(refId), ConsistencyLevels.CAUSAL))
//							addUpdates(rawRows)
							None
					}

					if (unresolvedSet.size < unresolved.size)
						//If there are some dependencies still unresolved
						return optionalUpdate
					else
						//If all dependencies have been resolved
						return Some(latestUpdate)

				//If the key could not be found all together, then we can not read it
				case NotFound() =>
					return None
			}

			return handleCausalReadRec(key0, Set.empty)
		}

		private def addUpdates(updates : Seq[Update[Id, Key, Data]]) : Unit = {
			updates.foreach(upd => sessionOrder.graph.addUpdate(upd))
		}

		private def handleWrite(baseTx : BaseTxContext)(id : Id, key : Key, data : Data, consistency: Consistency): Update[Id, Key, Data] = {
			if (consistency == ConsistencyLevels.LOCAL) {
				throw new UnsupportedConsistencyLevelException(consistency)
			}

			val update = sessionOrder.lockUpdate(id, key, data)
			try {
				baseTx.write(key, update, CassandraWriteParams(consistency))
				sessionOrder.confirmUpdate()
				return update

			} catch {
				case e : Exception =>
					sessionOrder.releaseUpdate()
					//rethrow exception to stop the whole transaction.
					throw e
			}
		}


		private def convertRead(maybeUpdate : Option[Update[Id, Key, Data]]) : Read = maybeUpdate match {
			case None => convertNone
			case Some(upd) => convertResult(upd)
		}


		trait ShimTxContext extends TxContext

		class SysnameShimNoneTxContext(val baseTx : BaseTxContext) extends ShimTxContext {
			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = Ids.freshId()
				handleWrite(baseTx)(id, key, data, consistency)
			}


			def read(key : Key, consistency : Consistency) : Read = {
				convertRead(handleRead(baseTx)(key, consistency))
			}
		}

		class SysnameShimReadUncommittedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {
			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = Ids.freshId()
				handleWrite(baseTx)(id, key, data, consistency)
			}

			def read(key : Key, consistency : Consistency) : Read = {
				convertRead(handleRead(baseTx)(key, consistency))
			}
		}

		class SysnameShimReadCommittedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {

			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = Ids.freshId()
				handleWrite(baseTx)(id, key, data, consistency)
			}


			def read(key : Key, consistency : Consistency) : Read = {
				convertRead(handleRead(baseTx)(key, consistency))
			}
		}

		class SysnameShimSnapshotIsolatedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {

			//TODO: Snap shots are not created using the consistency level (e.g. what is a causal snapshot?)

			private val readCache : mutable.Map[Key, Option[Update[Id, Key, Data]]] = mutable.HashMap.empty

			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = Ids.freshId()
				val update = handleWrite(baseTx)(id, key, data, consistency)
				readCache.put(key, Some(update))
			}

			def read(key : Key, consistency : Consistency) : Read = readCache.get(key) match {
				//The key was not found -> read from the underlying store
				case None => handleRead(baseTx)(key, consistency) match {
					//The underlying store did not return a valid read
					case None =>
						readCache.put(key, None)
						return convertNone
					//The underlying did return something
					case Some(upd) =>
						readCache.put(key, Some(upd))
						return convertResult(upd)
				}

				//There was already an entry in the local cache
				case Some(maybeUpd) => maybeUpd match {
					//The cached value was none (i.e. the last read from that key returned none)
					case None =>
						return convertNone
					//There was some real value cached
					case Some(upd) =>
						return convertResult(upd)
				}
			}
		}

		override def print() : Unit = {
			Log.info(classOf[SysnameShimSessionContext], sessionOrder.toString)
		}
	}
}

*/



