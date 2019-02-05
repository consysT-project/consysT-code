package de.tudarmstadt.consistency.storelayer.local

import de.tudarmstadt.consistency.storelayer.distribution.{DatastoreService, IdService, SessionService, TxidService}
import de.tudarmstadt.consistency.storelayer.local.LocalLayerInterface.AbortedException
import de.tudarmstadt.consistency.storelayer.local.dependency.Session
import de.tudarmstadt.consistency.storelayer.local.exceptions.UnsupportedConsistencyLevelException

/**
	* Created on 28.01.19.
	*
	* @author Mirko Köhler
	*/
trait LocalLayerImpl[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] extends LocalLayerInterface[Key, Data, Isolation, Consistency] {


	val store : SessionService[_, _, Key, Data, _, Isolation, Consistency]
		with DatastoreService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency]
		with IdService[Id]
		with TxidService[Txid]
	import store._

	val session : Session[Id, Key, Data, Txid]

	trait TransactionCtxImpl extends TransactionCtx {
		protected def handleRead(consistency : Consistency, key : Key) : Option[Data] =
			throw new UnsupportedConsistencyLevelException[Consistency](consistency)

		protected def handleWrite(consistency : Consistency, opNode : OpNode[Id, Txid, Key, Data]) : Boolean =
			throw new UnsupportedConsistencyLevelException[Consistency](consistency)


		final def read(consistency : Consistency, key : Key) : Option[Data] = ???


		override final def write(consistency : Consistency, key : Key, data : Data) : Unit = {
			val id = freshId()
			val opNode = session.lockUpdate(id, key, data)

			if (handleWrite(consistency, opNode)) {
				session.confirmUpdate()
			} else {
				session.releaseUpdate()
			}

		}
	}
}
