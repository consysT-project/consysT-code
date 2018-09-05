package de.tudarmstadt.consistency.store.shim

import com.datastax.driver.core.ResultSet
import de.tudarmstadt.consistency.store._
import de.tudarmstadt.consistency.store.cassandra.DataRow
import de.tudarmstadt.consistency.store.shim.Event.{Tx, Update}
import de.tudarmstadt.consistency.store.shim.EventOrdering.{ReadResult, Resolved, SessionOrder}
import de.tudarmstadt.consistency.utils.Log

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameVersionedStore[Id, Key, Data, TxStatus, Isolation, Consistency, Read] extends StoreInterface[Key, Data, Unit, Isolation, Consistency, Consistency, Read] {

	override type SessionCtx = SysnameShimSessionContext
	type BaseSessionContext = baseStore.SessionContext

	implicit val idOrdering : Ordering[Id]

	val baseStore : StoreInterface[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraWriteParams[Id, Key, Consistency], CassandraReadParams[Consistency], Seq[DataRow[Id, Key, Data, TxStatus, Isolation, Consistency]]]
	val converter : RowConverter[Event[Id, Key, Data]]

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

		private val sessionOrder : SessionOrder[Id, Key, Data] = EventOrdering.newSessionOrder


		override def startTransaction[U](isolation : Isolation)(f : Transaction[U]) : Option[U] = {
			val txid = idOps.freshId()
			val txParams = CassandraTxParams(txid, isolation)

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

		override def refresh() : Unit = {
			val results = baseSession.refresh()

			converter.resultSetForeach(results, {
				case upd@Update(id, key, _, _, _) => sessionOrder.addRaw(id, key, upd)
				case tx@Tx(id, _) => sessionOrder.addRaw(id, tx)
			})
		}


		private [shim] def addRaws(rows : Seq[DataRow[Id, Key, Data, _, _, _]]) : Unit = {
			rows.foreach(row => {
				val key = row.key

				if (key == keyOps.transactionKey) {
					val id = row.id
					val deps = row.deps

					sessionOrder.addRaw(id, Tx(id, deps))
				} else {
					val id = row.id
					val data = row.data
					val deps = row.deps
					val txid = row.txid

					sessionOrder.addRaw(id, key, Update(id, key, data, txid, deps))
				}
			})

		}

		private def resolveRead(baseTx : BaseTxContext)(key : Key, consistency : Consistency) : Read = {
			val rows = baseTx.read(key, CassandraReadParams(consistency))
			addRaws(rows)

			sessionOrder.readResolved(key) match {
				case Resolved(upd, _, _) => convertResult(upd)
				case _ => convertNone
			} //TODO: if the key cannot be resolved, try to read rows that are needed for resolution
		}

		trait ShimTxContext extends TxContext

		class SysnameShimNoneTxContext(val baseTx : BaseTxContext) extends ShimTxContext {
			def update(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = idOps.freshId()
				val deps = sessionOrder.getNextDependencies

				val opParams = CassandraWriteParams(id, deps, consistency)

				baseTx.update(key, data, opParams)

				sessionOrder.addUpdate(id, key, data)
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

				baseTx.update(key, data, opParams)

				sessionOrder.addUpdate(id, key, data)
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





