package de.tudarmstadt.consistency.store.scala.extra

import de.tudarmstadt.consistency.store.scala.extra.internalstore.{CassandraSession, CommitStatus, ReadStatus}

import scala.reflect.runtime.universe._

/**
	* Created on 28.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameStore[Id, Key, Data, TxStatus, Consistency, Isolation] {

	type Context = TransactionContext

	//The result R of a transaction is either some value or an abort (None)
	type Transaction[R] = Context => Option[R]

	trait TransactionContext {
		def read(key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Option[Data]
		def write(key : Key, data : Data)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : Unit
	}

	def commit[Return](session : CassandraSession, transaction : Transaction[Return], isolation : Isolation)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : CommitStatus[Id, Return]


	protected def read(session : CassandraSession, key : Key)(implicit idTT : TypeTag[Id], keyTT : TypeTag[Key], dataTT : TypeTag[Data], txStatusTT : TypeTag[TxStatus], consistencyTT : TypeTag[Consistency], isolationTT : TypeTag[Isolation]) : ReadStatus[Id, Key, Data]

	def newSession : CassandraSession


	/* Operations on for the various data types */

	protected trait IdOps[T] {
		def freshId() : T
	}

	protected trait TxStatusOps[T] {
		def pending : T
		def committed : T
		def aborted : T
	}

	protected trait IsolationLevelOps[T] {
		def snapshotIsolation : T
		def readUncommitted : T
		def readCommitted : T
	}

	protected trait ConsistencyLevelOps[T] {
		def sequential : T
	}



	def idOps : IdOps[Id]
	def txStatusOps : TxStatusOps[TxStatus]
	def isolationLevelOps : IsolationLevelOps[Isolation]
	def consistencyLevelOps : ConsistencyLevelOps[Consistency]




}
