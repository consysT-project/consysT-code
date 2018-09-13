package de.tudarmstadt.consistency.store

import de.tudarmstadt.consistency.store.Store.{ISessionContext, ITxContext}

import scala.concurrent.{ExecutionContext, Future}
import scala.languageFeature.higherKinds

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait Store[Key, Data, TxParams, WriteParams, ReadParams, Read] {

	type SessionCtx <: SessionContext
	type Session[U] = SessionCtx => U

	def startSession[U](f : Session[U]) : U
	def close() : Unit

	trait SessionContext extends ISessionContext[TxParams] {
		type TxCtx <: TxContext
		type Transaction[U] = TxCtx => Option[U]

		trait TxContext extends ITxContext[Key, Data, WriteParams, ReadParams, Read]
	}

	/*
	Use this to start a parallel session on the store. Use this FOR TESTING PURPOSES ONLY and only start one parallel
	session per store! A store is expected to be accessed by a (logically) single threaded program!
	 */
	private[store] def parallelSession[U](session : Session[U])(implicit execCtx : ExecutionContext): Future[U] = {
		//Parallel
		val fut : Future[U] = Future {
				val u = startSession { sess =>
				//Commit a transaction
				session(sess)
			}
			u
		}
		fut
	}
}

object Store {
	trait ISessionContext[TxParams] {
		type Transaction[_]

		def startTransaction[U](params : TxParams)(f : Transaction[U]) : Option[U]
		def print() : Unit
	}

	trait ITxContext[Key, Data, WriteParams, ReadParams, Read] {
		def update(key : Key, data : Data, params : WriteParams) : Unit
		def read(key : Key, params : ReadParams) : Read
	}
}
