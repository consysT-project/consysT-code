package de.tudarmstadt.consistency.store.shim

import com.datastax.driver.core.exceptions.{NoHostAvailableException, QueryExecutionException}
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.{CassandraReadParams, CassandraTxParams, CassandraWriteParams}
import de.tudarmstadt.consistency.store.cassandra.exceptions.UnsupportedConsistencyLevelException
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}
import de.tudarmstadt.consistency.utils.Log

import scala.collection.mutable

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] extends Store[Key, Data, Isolation, Consistency, Consistency, Read] {

	override type SessionCtx = SysnameShimSessionContext
	type BaseSessionContext = baseStore.SessionContext

	implicit val idOrdering : Ordering[Id]

	val baseStore : Store[Key, Event[Id, Key, Data], CassandraTxParams[Id, Isolation], CassandraWriteParams[Consistency], CassandraReadParams[Id, Consistency], Seq[Event[Id, Key, Data]]]

	val ids : Ids[Id]
	val keys : Keys[Key]
	val txStatuses : TxStatuses[TxStatus]
	val isolationLevels : IsolationLevels[Isolation]
	val consistencyLevels : ConsistencyLevels[Consistency]

	override def startSession[U](f : Session[U]) : U = {
		baseStore.startSession { baseSession =>
			val session = new SysnameShimSessionContext(baseSession)
			f(session)
		}
	}

	override def close() : Unit = {
		baseStore.close()
	}

	override def initialize() : Unit = {
		baseStore.initialize()
	}

	override def reset(): Unit = {
		baseStore.reset()
	}

	def convertResult(upd : Update[Id, Key, Data]) : Read
	def convertNone : Read

	class SysnameShimSessionContext(val baseSession : BaseSessionContext) extends SessionContext {

		override type TxCtx = ShimTxContext
		type BaseTxContext = baseSession.TxContext

		private val sessionOrder : SessionOrder[Id, Key, Data] = new SessionOrder[Id, Key, Data]


		override def startTransaction[U](isolation : Isolation)(f : Transaction[U]) : Option[U] = {


			isolation match {
				case l if l == isolationLevels.none =>
					handleNonIsolatedTransactions(f, isolation, baseTx => new SysnameShimNoneTxContext(baseTx))

				case l if l == isolationLevels.readCommitted =>
					handleIsolatedTransaction(f, isolation, baseTx => new SysnameShimReadCommittedTxContext(baseTx))

				case l if l == isolationLevels.snapshotIsolation =>
					handleIsolatedTransaction(f, isolation, baseTx => new SysnameShimSnapshotIsolatedTxContext(baseTx))

			}
		}

		private def handleNonIsolatedTransactions[U](f : Transaction[U], isolation : Isolation, makeCtx : BaseTxContext => ShimTxContext) : Option[U] = {
			val txid = ids.freshId()
			val txParams = CassandraTxParams(Some(TxRef(txid)), isolation)

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
			val txid = ids.freshId()
			val txParams = CassandraTxParams(Some(TxRef(txid)), isolation)

			//Start the transaction in this session
			sessionOrder.startTransaction(txid)

			try {
				//Start a transaction in the base store
				baseSession.startTransaction(txParams) { baseTx =>
					val txContext = makeCtx(baseTx)
					val res = f(txContext) //execute the transaction as defined by the user

					//Lock the transaction and add the transaction record to the base store
					val tx = sessionOrder.lockTransaction()
					//TODO: Which consistency level do we use when writing the tx record.
					baseTx.write(keys.transactionKey, tx, CassandraWriteParams(consistencyLevels.causal))

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
			case l if l == consistencyLevels.causal => handleCausalRead(baseTx)(key)
			case l if l == consistencyLevels.weak => handleWeakRead(baseTx)(key)
			case _ => throw new UnsupportedConsistencyLevelException(consistency)
		}


		private def handleWeakRead(baseTx : BaseTxContext)(key : Key) : Option[Update[Id, Key, Data]] = {
			val rows = baseTx.read(key, CassandraReadParams(None, consistencyLevels.weak))
			addEvents(rows)

			sessionOrder.resolve(key) match {
				//If we got some value, just return the latest one (without checking any dependencies)
				case Found(_, latestUpdate, _) =>
					sessionOrder.addRead(latestUpdate.toRef)
					return Some(latestUpdate)

				//If the key could not be found, then we can not read it
				case _ =>
					return None
			}
		}

		private def handleCausalRead(baseTx : BaseTxContext)(key : Key) : Option[Update[Id, Key, Data]] = {
			val rows = baseTx.read(key, CassandraReadParams(None, consistencyLevels.causal))
			addEvents(rows)

			var alreadyTried : Set[Id] = Set.empty

			//Iterate until all (transitive) dependencies have been fetched (or at least tried)
			while (true) {
				sessionOrder.resolve(key) match {
					//If we read a resolved value and that value is already the latest, we can just return that value
					case Found(Some(resolvedUpdate), latestUpdate, _) if resolvedUpdate == latestUpdate =>
						sessionOrder.addRead(resolvedUpdate.toRef)
						return Some(resolvedUpdate)
					//If we have a resolved value but there is a newer value that has not been resolved yet
					case Found(optionalUpdate, latestUpdate, unresolved) =>
						//..., then try to resolve it
						unresolved.foreach(evt => {
							val evtKey = evt match {
								case UpdateRef(_, refKey) => refKey
								case TxRef(_) => keys.transactionKey
							}

							//if the key has already been updated in this run, then abort this read and return the version that could have been resolved
							if (alreadyTried.contains(evt.id)) {
								optionalUpdate match {
									//If there was another resolved update, then return it
									case Some(resolvedUpdate) =>
										sessionOrder.addRead(resolvedUpdate.toRef)
										return Some(resolvedUpdate)
									//else return nothing
									case None =>
										return None
								}
							}

							val rawRows = baseTx.read(evtKey, CassandraReadParams(Some(evt.id), consistencyLevels.causal))
							addEvents(rawRows)
							alreadyTried = alreadyTried + evt.id
						})
						//now, retry to read the key

					//If the key could not be found all together, then we can not read it
					case NotFound() =>
						return None
				}
			}

			//fallback case: this code should never be executed
			assert(assertion = false, "Oh no! How could this have been executed?! You're a wizard, Harry!")
			return None
		}

		private def addEvents(events : Seq[Event[Id, Key, Data]]) : Unit = {
			events.foreach(event => sessionOrder.graph.add(event))
		}

		private def handleWrite(baseTx : BaseTxContext)(id : Id, key : Key, data : Data, consistency: Consistency): Update[Id, Key, Data] = {
			val update = sessionOrder.lockUpdate(id, key, data)
			try {
				baseTx.write(key, update, CassandraWriteParams(consistency))
				sessionOrder.confirmUpdate()
				return update
				//			} catch {
				//				/*
				//					TODO: Do we want to handle exceptions at an operation level?
				//				  At the moment we catch the exception here and abort the write.
				//				  Another possibility would be to catch the exception at the transaction level
				//				  and thus abort the whole transaction.
				//				 */
				//				case e : NoHostAvailableException =>
				//					e.printStackTrace()
				//					sessionOrder.releaseUpdate()
				//				case e : QueryExecutionException =>
				//					//TODO: Differentiate between different errors here. What to do if the write was accepted partially?
				//					e.printStackTrace()
				//					sessionOrder.releaseUpdate()
				//			}
			} catch {
				case e : Exception =>
					sessionOrder.releaseUpdate()
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
				val id = ids.freshId()
				handleWrite(baseTx)(id, key, data, consistency)
			}


			def read(key : Key, consistency : Consistency) : Read = {
				convertRead(handleRead(baseTx)(key, consistency))
			}
		}

		class SysnameShimReadCommittedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {

			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = ids.freshId()
				handleWrite(baseTx)(id, key, data, consistency)
			}


			def read(key : Key, consistency : Consistency) : Read = {
				convertRead(handleRead(baseTx)(key, consistency))
			}
		}

		class SysnameShimSnapshotIsolatedTxContext(val baseTx : BaseTxContext) extends ShimTxContext {

			private val readCache : mutable.Map[Key, Update[Id, Key, Data]] = mutable.HashMap.empty

			def write(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = ids.freshId()
				val update = handleWrite(baseTx)(id, key, data, consistency)
				readCache.put(key, update)
			}

			def read(key : Key, consistency : Consistency) : Read = readCache.get(key) match {
				case None => handleRead(baseTx)(key, consistency) match {
					case None =>
						return convertNone
					case Some(upd) =>
						readCache.put(key, upd)
						return convertResult(upd)
				}

				case Some(upd) =>
					return convertResult(upd)
			}
		}

		override def print() : Unit = {
			Log.info(classOf[SysnameShimSessionContext], sessionOrder.toString)
		}
	}
}





