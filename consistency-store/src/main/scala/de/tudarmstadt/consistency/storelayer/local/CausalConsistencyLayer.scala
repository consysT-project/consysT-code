package de.tudarmstadt.consistency.storelayer.local

import com.datastax.driver.core.exceptions.{NoHostAvailableException, QueryExecutionException}
import de.tudarmstadt.consistency.storelayer.distribution._
import de.tudarmstadt.consistency.storelayer.local.protocols.SnapshotIsolatedTransactionProtocol

import scala.collection.mutable

/**
	* Created on 16.01.19.
	*
	* @author Mirko Köhler
	*/
trait CausalConsistencyLayer[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
	extends LocalLayer[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {

		override protected val store :  SessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
			with IdService[Id]
			with TxidService[Txid]
			with DatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
			with ConsistencyBindings[Consistency]

		import store._


	override private[local] def handleWrite(consistency : Consistency, opNode : OpNode[Id, Txid, Key, Data]) : Boolean = consistency match {
		case x if x == Consistency.CAUSAL =>
			//TODO: Do anything here?
			super.handleWrite(consistency, opNode)

		case _ =>
			super.handleWrite(consistency, opNode)
	}


	}
