package de.tudarmstadt.consistency.store.scala.extra

import scala.util.Random

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
object Util {
	trait IdOps[T] {
		def freshId() : T
	}

	trait KeyOps[T] {
		def transactionKey : T
	}

	trait TxStatusOps[T] {
		def pending : T
		def committed : T
		def aborted : T
	}

	trait IsolationLevelOps[T] {
		def snapshotIsolation : T
		def readUncommitted : T
		def readCommitted : T
		def none : T
	}

	trait ConsistencyLevelOps[T] {
		def sequential : T
	}


	trait CommitStatus[Id, Return]
	object CommitStatus {
		//The transaction successfully committed
		case class Success[Id, Return](txid : Id, writtenIds : Set[Id], result : Return) extends CommitStatus[Id, Return]

		//The transaction has been aborted and changes have been rolled back.
		case class Abort[Id, Return](txid : Id, description : String) extends CommitStatus[Id, Return]

		//The transaction indicated an error. It is unclear whether it (partially) committed or aborted comnpletely.
		case class Error[Id, Return](txid : Id, error : Throwable) extends CommitStatus[Id, Return]

	}

	trait ReadStatus[Id, Key, Data]
	object ReadStatus {
		case class Success[Id, Key, Data](key : Key, id : Id, data : Data, deps : Set[Id]) extends ReadStatus[Id, Key, Data]
		case class NotFound[Id, Key, Data](key : Key, description : String) extends ReadStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends ReadStatus[Id, Key, Data]
	}

	trait WriteStatus[Id, Key, Data]
	object WriteStatus {
		case class Success[Id, Key, Data](id : Id, key : Key, data : Data) extends WriteStatus[Id, Key, Data]
		case class Error[Id, Key, Data](key : Key, e : Throwable) extends WriteStatus[Id, Key, Data]
	}

	case class CUpdate[Id, Data](id : Id, data : Data, deps : Set[Id])

	case class CassandraOpParams[Id, Consistency](id : Id, deps : Set[Id], consistency : Consistency)
	case class CassandraTxParams[Id, Isolation](txid : Id, isolation : Isolation)


	object SimpleTypeFactories {



	}

}
