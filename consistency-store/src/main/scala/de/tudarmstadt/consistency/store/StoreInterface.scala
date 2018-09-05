package de.tudarmstadt.consistency.store

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait StoreInterface[Key, Data, RefreshResult, TxParams, WriteParams, ReadParams, ReadResult] {

	type SessionCtx <: SessionContext
	type Session[U] = SessionCtx => U

	def startSession[U](f : Session[U]) : U

	trait SessionContext {

		type TxCtx <: TxContext
		type Transaction[U] = TxCtx => Option[U]

		def startTransaction[U](params : TxParams)(f : Transaction[U]) : Option[U]
		def refresh() : RefreshResult
		def print() : Unit

		trait TxContext {
			def update(key : Key, data : Data, params : WriteParams) : Unit
			def read(key : Key, params : ReadParams) : ReadResult
		}
	}


}
