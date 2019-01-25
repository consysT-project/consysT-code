package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import com.datastax.driver.core.{ConsistencyLevel, WriteType}
import com.datastax.driver.core.exceptions.WriteTimeoutException
import com.datastax.driver.core.querybuilder.QueryBuilder
import de.tudarmstadt.consistency.storelayer.distribution.{ConsistencyBindings, CoordinationService, SessionService, TxStatusBindings}

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraCoordinationService[Txid, TxStatus, Isolation] extends CoordinationService[Txid, TxStatus, Isolation] {
	self : CassandraSessionService[_, Txid, _, _, TxStatus, Isolation, _] with TxStatusBindings[TxStatus] =>
	import typeBinding._

	private val casTxTableName : String = "t_cas_tx"


	/* queries */
	def CREATE_CAS_TX_TABLE(): Unit = {
		session.execute(
			s"""CREATE TABLE $casTxTableName
				 | (txid ${TypeCodecs.Id.getCqlType.asFunctionParameterString},
				 | status ${TypeCodecs.TxStatus.getCqlType.asFunctionParameterString},
				 | isolation ${TypeCodecs.Isolation.getCqlType.asFunctionParameterString},
				 | PRIMARY KEY(txid))""".stripMargin
		)
	}


	/* operations */
	override def addNewTransaction(txid : Txid, txStatus : TxStatus, isolation : Isolation) : Boolean = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val txInsertResult = session.execute(
			insertInto(casTxTableName)
				.values(
					Array[String]("txid", "status", "isolation"),
					Array[AnyRef](txid.asInstanceOf[AnyRef], txStatus.asInstanceOf[AnyRef], isolation.asInstanceOf[AnyRef])
				)
				.ifNotExists()
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		val txInsertResultRow = txInsertResult.one()
		assert(txInsertResultRow != null)

		//1.a. If the transaction id was already in use abort!
		txInsertResult.wasApplied()
	}

	override def abortIfPending(txid : Txid) : Boolean = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val updateOtherTxResult = session.execute(
			update(casTxTableName)
				.`with`(set("status", TxStatus.ABORTED))
				.where(QueryBuilder.eq("txid", txid))
				.onlyIf(QueryBuilder.ne("status", TxStatus.COMMITTED))
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		updateOtherTxResult.wasApplied()
	}

	override def commitIfPending(txid : Txid) : Boolean = {
		import com.datastax.driver.core.querybuilder.QueryBuilder._

		val updateOtherTxResult = session.execute(
			update(casTxTableName)
				.`with`(set("status", TxStatus.COMMITTED))
				.where(QueryBuilder.eq("txid", txid))
				.onlyIf(QueryBuilder.ne("status", TxStatus.ABORTED))
				.setConsistencyLevel(ConsistencyLevel.ALL)
		)

		updateOtherTxResult.wasApplied()
	}

	override def forceCommitIfPending(txid : Txid) : Boolean = {

		while (true) {
			try {
 				val wasCommitted = commitIfPending(txid)
				return wasCommitted
			} catch {
				//when a timeout exception with write type CAS is thrown, then it is unclear whether the write has succeeded
				//Therefore, we should retry committing the update...
				//TODO: Add some measure to avoid infinite loops
				//TODO: This is only available for cassandra stores. The whole loop is designed for Cassandra. Remove it here!
				case e : WriteTimeoutException if e.getWriteType == WriteType.CAS =>
					System.err.println("commit retry!")
					//Wait a bit, then retry
					Thread.sleep(300)
			}
		}

		sys.error("?????")
	}


}
