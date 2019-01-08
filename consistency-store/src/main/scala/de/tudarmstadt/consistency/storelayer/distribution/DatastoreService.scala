package de.tudarmstadt.consistency.storelayer.distribution

import com.datastax.driver.core.{Row, TupleValue}

import scala.collection.JavaConverters

/**
	* Created on 08.01.19.
	*
	* @author Mirko Köhler
	*/
trait DatastoreService[Id, Key, Data, TxStatus, Isolation, Consistency] {
	self : SessionService[Id, Key, Data, TxStatus, Isolation, Consistency] =>

	/* rows that have been read from the store */
	trait OpRow {
		def id : Id
		def key : Key
		def data : Data
		def txid : Option[TxRef]
		def deps : Set[OpRef]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency
	}

	trait TxRow {
		def id : Id
		def deps : Set[OpRef]
		def txStatus : TxStatus
		def isolation : Isolation
		def consistency : Consistency
	}


	case class DataWrite(id : Id, key : Key, data : Data, txid : Option[TxRef], dependencies : Set[OpRef], consistency : Consistency)

	case class TxWrite(id : Id, dependencies : Set[OpRef], consistency : Consistency)


	def writeData(dataWrite : DataWrite, txStatus : TxStatus, isolation : Isolation) : Unit = {
		import dataWrite._
		writeData(id, key, data, txid, dependencies, txStatus, isolation, consistency)
	}

	def writeData(id : Id, key : Key, data : Data, txid : Option[TxRef], dependencies : Set[OpRef], txStatus : TxStatus, isolation : Isolation, consistency : Consistency) : Unit

	//Optional
	def updateTxStatusInData(id : Id, key : Key, txStatus : TxStatus) : Unit

	def deleteData(id : Id, key : Key) : Unit

	def readData(id : Id, key : Key) : Option[OpRow]

	def readAllData(key : Key) : Iterable[OpRow]

	def writeTx(txWrite: TxWrite, txStatus : TxStatus, isolation : Isolation) : Unit = {
		import txWrite._
		writeTx(id, dependencies, txStatus, isolation, consistency)
	}
	def writeTx(id : Id, dependencies : Set[OpRef], txStatus : TxStatus, isolation : Isolation, consistency : Consistency) : Unit

	def deleteTx(id : Id) : Unit

	def readTx(id : Id) : Option[TxRow]

}
