package de.tudarmstadt.consistency.store.shim

import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.shim.Event.Update
import de.tudarmstadt.consistency.store.shim.EventRef.{TxRef, UpdateRef}
import de.tudarmstadt.consistency.store.shim.Resolved.{Found, NotFound}
import de.tudarmstadt.consistency.utils.Log

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] extends Store[Key, Data, Isolation, Consistency, Consistency, Read] {

	override type SessionCtx = SysnameShimSessionContext
	type BaseSessionContext = baseStore.SessionContext

	implicit val idOrdering : Ordering[Id]

	val baseStore : Store[Key, Event[Id, Key, Data], CassandraTxParams[Id, Isolation], CassandraWriteParams[Id, Key, Consistency], CassandraReadParams[Id, Consistency], Seq[Event[Id, Key, Data]]]

	val idOps : IdOps[Id]
	val keyOps : KeyOps[Key]
	val txStatusOps : TxStatusOps[TxStatus]
	val isolationLevelOps : IsolationLevelOps[Isolation]
	val consistencyLevelOps : ConsistencyLevelOps[Consistency]

	override def startSession[U](f : Session[U]) : U = {
		baseStore.startSession { baseSession =>
			val session = new SysnameShimSessionContext(baseSession)
			f(session)
		}
	}

	override def close() : Unit = {
		baseStore.close()
	}

	def convertResult(upd : Update[Id, Key, Data]) : Read
	def convertNone : Read

	class SysnameShimSessionContext(val baseSession : BaseSessionContext) extends SessionContext {

		override type TxCtx = ShimTxContext
		type BaseTxContext = baseSession.TxContext

		private val sessionOrder : SessionOrder[Id, Key, Data] = new SessionOrder[Id, Key, Data]


		override def startTransaction[U](isolation : Isolation)(f : Transaction[U]) : Option[U] = {
			val txid = idOps.freshId()
			val txParams = CassandraTxParams(Some(TxRef(txid)), isolation)

			isolation match {
				case l if l == isolationLevelOps.none =>
					val transactionState = baseSession.startTransaction(txParams) { baseTx =>
						val tx = new SysnameShimNoneTxContext(baseTx)
						f(tx)
					}

					transactionState match {
						case None =>
							assert(false, "a 'none'-isolated transaction can not be aborted")
							None
						case opt@Some(u) =>
							opt
					}

				case _ =>
					sessionOrder.startTransaction(txid)

					val transactionState = baseSession.startTransaction(txParams) { baseTx =>
						val tx = new SysnameShimDefaultTxContext(baseTx, isolation)
						f(tx)
						baseTx.update(keyOps.transactionKey, )
					}

					transactionState match {
						case None =>
							sessionOrder.abortTransaction()
							None
						case opt@Some(u) =>
							sessionOrder.commitTransaction()
							opt
					}
			}

		}



		private [shim] def addEvents(events : Seq[Event[Id, Key, Data]]) : Unit = {
			events.foreach(event => sessionOrder.graph.add(event))
		}

		private def resolveRead(baseTx : BaseTxContext)(key : Key, consistency : Consistency) : Read = {
			val rows = baseTx.read(key, CassandraReadParams(None, consistency))
			addEvents(rows)

			var alreadyTried : Set[Id] = Set.empty

			while (true) {
				sessionOrder.getResolved(key) match {
					//If we read a resolved value and that value is already the latest, we can just return that value
					case Found(Some(resolvedUpdate), latestUpdate, _) if resolvedUpdate == latestUpdate =>
						sessionOrder.addRead(resolvedUpdate.toRef)
						return convertResult(resolvedUpdate)
					//If we have a resolved value but there is a newer value that has not been resolved yet
					case Found(optionalUpdate, latestUpdate, unresolved) =>
						//..., then try to resolve it
						unresolved.foreach(evt => {
							val evtKey = evt match {
								case UpdateRef(_, refKey) => refKey
								case TxRef(_) => keyOps.transactionKey
							}

							//if the key has already been updated in this run, then abort this read and return the version that could have been resolved
							if (alreadyTried.contains(evt.id)) {
								optionalUpdate match {
									//If there was another resolved update, then return it
									case Some(resolvedUpdate) =>
										sessionOrder.addRead(resolvedUpdate.toRef)
										return convertResult(resolvedUpdate)
									//else return nothing
									case None =>
										return convertNone
								}
							}

							val rawRows = baseTx.read(evtKey, CassandraReadParams(Some(evt.id), consistency))
							addEvents(rawRows)
							alreadyTried = alreadyTried + evt.id
						})
						//now, retry to read the key

					//If the key could not be found all together, then we can not read it
					case NotFound() =>
						return convertNone
				}
			}

			//fallback case: this code should never be executed
			assert(false, "Oh no! How could this have been executed?! You're a wizard, Harry!")
			return convertNone

		}





		trait ShimTxContext extends TxContext

		class SysnameShimNoneTxContext(val baseTx : BaseTxContext) extends ShimTxContext {
			def update(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = idOps.freshId()
				val deps = sessionOrder.getNextDependencies

				val opParams = CassandraWriteParams(id, deps, consistency)

				val update = sessionOrder.lockNextUpdate(id, key, data)
				baseTx.update(key, update, opParams)
				//TODO: Handle errors of base update
				sessionOrder.confirmNextUpdate()
			}


			def read(key : Key, consistency : Consistency) : Read = {
				resolveRead(baseTx)(key, consistency)
			}
		}

		class SysnameShimDefaultTxContext(val baseTx : BaseTxContext, val isolation: Isolation) extends ShimTxContext {

			def update(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = idOps.freshId()
				val deps = sessionOrder.getNextDependencies

				val opParams = CassandraWriteParams(id, deps, consistency)

				val update = sessionOrder.lockNextUpdate(id, key, data)
				baseTx.update(key, update, opParams)
				//TODO: Handle errors of base update
				sessionOrder.confirmNextUpdate()
			}


			def read(key : Key, consistency : Consistency) : Read = {
				resolveRead(baseTx)(key, consistency)
			}
		}

		override def print() : Unit = {
			Log.info(classOf[SysnameShimSessionContext], sessionOrder.toString)
		}
	}
}





