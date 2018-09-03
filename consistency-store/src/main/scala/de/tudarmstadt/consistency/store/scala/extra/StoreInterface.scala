package de.tudarmstadt.consistency.store.scala.extra

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/
trait StoreInterface[Key, Data, Update, TxParams, WriteParams, ReadParams, ReadResult] {

	type Session[U] = SessionContext => U

	def startSession[U](f : Session[U]) : U

	trait SessionContext {

		type Transaction[U] = TxContext => Option[U]

		def startTransaction[U](params : TxParams)(f : Transaction[U]) : Option[U]
		def update() : Update
		def print() : Unit

		trait TxContext {
			def update(key : Key, data : Data, params : WriteParams) : Unit
			def read(key : Key, params : ReadParams) : ReadResult
		}
	}


}
