package de.tudarmstadt.consistency.store.scala.extra.shim

import com.datastax.driver.core.querybuilder.QueryBuilder
import com.datastax.driver.core.{ResultSet, Session}
import de.tudarmstadt.consistency.store.scala.extra.{RowConverter, StoreInterface, runtimeClassOf}
import de.tudarmstadt.consistency.store.scala.extra.Util._
import de.tudarmstadt.consistency.store.scala.extra.shim.EventOrdering.{Event, SessionOrder, Tx, Update}
import de.tudarmstadt.consistency.utils.Log

import scala.collection.JavaConverters

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameVersionedStore[Id, Key, Data, Isolation, Consistency] extends StoreInterface[Key, Data, Unit, Isolation, Consistency] {

	type BaseSessionContext = baseStore.SessionContext

	implicit val idOrdering : Ordering[Id]

	val baseStore : StoreInterface[Key, Data, ResultSet, CassandraTxParams[Id, Isolation], CassandraOpParams[Id, Consistency]]
	val converter : RowConverter[Event[Id, Key, Data]]

	val idOps : IdOps[Id]
	val isolationLevelOps : IsolationLevelOps[Isolation]
	val consistencyLevelOps : ConsistencyLevelOps[Consistency]

	def startSession[U](f : SessionContext => U) : U = {
		baseStore.startSession { baseSession =>
			val session = new SysnameShimSessionContext(baseSession)
			f(session)
		}
	}


	class SysnameShimSessionContext(val baseSession : BaseSessionContext) extends SessionContext {

		type BaseTxContext = baseSession.TxContext

		private val sessionOrder : SessionOrder[Id, Key, Data] = EventOrdering.newSessionOrder


		override def startTransaction[U](isolation : Isolation)(f : TxContext => Option[U]) : Option[U] = {
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

		override def update() : Unit = {
			val results = baseSession.update()

			converter.resultSetForeach(results, {
				case upd@Update(id, key, _, _, _) => sessionOrder.addRaw(id, key, upd)
				case tx@Tx(id, _) => sessionOrder.addRaw(id, tx)
			})



		}

		class SysnameShimNoneTxContext(val baseTx : BaseTxContext) extends TxContext {
			def update(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = idOps.freshId()
				val deps = sessionOrder.getNextDependencies

				val opParams = CassandraOpParams(id, deps, consistency)

				baseTx.update(key, data, opParams)

				sessionOrder.addUpdate(id, key, data)
			}


			def read(key : Key, consistency : Consistency) : Option[Data] = {
				sessionOrder.readResolved(key).map(_._2)
			}
		}

		class SysnameShimDefaultTxContext(val baseTx : BaseTxContext, val isolation: Isolation) extends TxContext {
			def update(key : Key, data : Data, consistency : Consistency) : Unit = {
				val id = idOps.freshId()
				val deps = sessionOrder.getNextDependencies

				val opParams = CassandraOpParams(id, deps, consistency)

				baseTx.update(key, data, opParams)

				sessionOrder.addUpdate(id, key, data)
			}


			def read(key : Key, consistency : Consistency) : Option[Data] = {
				sessionOrder.readResolved(key).map(_._2)
			}
		}

		override def print() : Unit = {
			Log.info(classOf[SysnameShimSessionContext], sessionOrder.toString)
		}
	}
}





