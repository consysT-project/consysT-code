package de.tudarmstadt.consistency.storelayer.local

import com.datastax.driver.core.exceptions.{NoHostAvailableException, QueryExecutionException}
import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.protocols.SnapshotIsolatedTransactionProtocol
import de.tudarmstadt.consistency.storelayer.local.protocols.TransactionProtocol.{Abort, Success}

import scala.collection.mutable

/**
	* Created on 16.01.19.
	*
	* @author Mirko Köhler
	*/
trait SnapshotIsolatedTransactionsLayer[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	extends LocalLayerImpl[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with SnapshotIsolatedTransactionProtocol[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {

	override protected val store :  SessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with IdService[Id]
		with TxidService[Txid]
		with DatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with CoordinationService[Txid, TxStatus, Isolation]
		with OptimisticLockService[Id, Txid, Key]
		with TxStatusBindings[TxStatus]
		with ConsistencyBindings[Consistency]
		with IsolationBindings[Isolation]

	import store._


	override protected def createTransaction[B](isolation : Isolation, txid : Txid) : TransactionCtx[B] =
		isolation match {
			case x if x == Isolation.SI => new SnapshotIsolatedTransaction(txid)
			case _ => super.createTransaction[B](isolation, txid)
		}


	private class SnapshotIsolatedTransaction[B](val txid : Txid) extends TransactionCtxImpl[B] {
		/* buffers all writes so that they can be applied at the end of the transaction */
		private val writeBuffer : mutable.Buffer[DataWrite] = mutable.Buffer.empty
		/* locally stores already read nodes */
		private val readMap : mutable.Map[Key, Set[OpNode[Id, Txid, Key, Data]]] = mutable.Map.empty


		def apply(f : () => B) : Option[B] = {
			try {
				val res = f.apply()

				val txNode = session.lockTransaction()
				commitWrites(TxWrite(txid, txNode.dependencies, Consistency.CAUSAL), writeBuffer)

				return Some(res)

			} catch {
				case e : AbortedException =>
					//the transaction has been aborted by the user
					None

				/* Cassandra related exception. TODO: move this somewhere else */
				case e : NoHostAvailableException =>
					e.printStackTrace()
					None
				case e : QueryExecutionException =>
					//TODO: Differentiate between different errors here. What to do if the write was accepted partially?
					e.printStackTrace()
					None
			}

		}

		override private[local] def handleWrite(consistency : Consistency, opNode : OpNode[Id, Txid, Key, Data]) : Boolean = {
			writeBuffer.append(DataWrite(opNode.id, opNode.key, opNode.data, Some(TxRef(txid)), opNode.dependencies, consistency))
			readMap.put(opNode.key, Set(opNode))
			true
		}

		override private[local] def handleAllRead(consistency: Consistency, key : Key) : Iterable[OpNode[Id, Txid, Key, Data]] = {
			val data : Iterable[OpRow] = store.readAllData(key)

			data.filter(row => readIsObservable(Some(txid), row) match {
				case Success => true
				case Abort(msg) =>
					Console.err.println(msg)
					false
			}).map(row => OpNode(row.id, row.key, row.data, row.txid, row.deps))
		}

	}

}
