package de.tudarmstadt.consistency.storelayer.local

import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.dependency.Session

import scala.collection.mutable

/**
	* Created on 25.01.19.
	*
	* @author Mirko Köhler
	*/
class LocalSnapshotIsolation[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	extends LocalLayerImpl[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {

	val store : SessionService[_, _, Key, Data, _, Isolation, Consistency]
		with DatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with IdService[Id]
		with TxidService[Txid]
	import store._

	val session : Session[Id, Key, Data, Txid]

	override protected def createCtx(isolation : Isolation) : TransactionCtx = {
		val txid = freshTxid()

		new SITransactionCtx(txid)
	}


	private class SITransactionCtx(val txid : Txid) extends TransactionCtxImpl {
		/* buffers all writes so that they can be applied at the end of the transaction */
		private val writeBuffer : mutable.Buffer[DataWrite] = mutable.Buffer.empty
		/* locally stores already read nodes */
	//	private val readMap : mutable.Map[Key, Set[OpNode[Id, Txid, Key, Data]]] = mutable.Map.empty

		protected def handleWrite(consistency : Consistency, opNode : OpNode[Id, Txid, Key, Data]) : Boolean = {
			writeBuffer.append(DataWrite(opNode.id, opNode.key, opNode.data, Some(TxRef(txid)), opNode.dependencies, consistency))
			super.handleWrite(consistency, opNode)
		}

	}

}
