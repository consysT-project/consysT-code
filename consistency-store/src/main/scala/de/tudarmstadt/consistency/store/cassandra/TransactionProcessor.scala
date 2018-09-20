package de.tudarmstadt.consistency.store.cassandra

import com.datastax.driver.core.Session
import de.tudarmstadt.consistency.store.cassandra.TransactionProcessor.CommitStatus
import de.tudarmstadt.consistency.store.shim.EventRef

import scala.reflect.runtime.universe._

/**
	* Created on 14.09.18.
	*
	* @author Mirko Köhler
	*/
trait TransactionProcessor {

	def commit[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag, Return](
		session : CassandraSession,
		store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
	)(
		txWrite : store.WriteTx,
		updWrites : Iterable[store.WriteUpdate]
	) : CommitStatus

	def isRowCommitted[Id : TypeTag, Key : TypeTag, Data : TypeTag, TxStatus : TypeTag, Isolation : TypeTag, Consistency : TypeTag](
	  session : CassandraSession,
    store : SysnameCassandraStore[Id, Key, Data, TxStatus, Isolation, Consistency]
  )(
    //an optional id of the transaction that reads the row
    txid : Option[Id],
    //the row that is checked whether it is committed
    row : store.DataRow
  ) : CommitStatus

}

object TransactionProcessor {

	trait CommitStatus {
		def isSuccess : Boolean
	}
	//The transaction successfully committed
	case object Success extends CommitStatus {
		override def isSuccess : Boolean = true
	}
	//The transaction has been aborted and changes have been rolled back.
	case class Abort(message : String) extends CommitStatus {
		override def isSuccess : Boolean = false
	}
}
