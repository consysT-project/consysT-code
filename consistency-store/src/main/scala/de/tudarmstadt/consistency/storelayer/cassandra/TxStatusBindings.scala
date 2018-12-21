package de.tudarmstadt.consistency.storelayer.cassandra

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait TxStatusBindings[TxStatus] {

	def TxStatus : TxStatusOps

	trait TxStatusOps {
		def ABORTED : TxStatus
		def COMMITTED : TxStatus
		def PENDING : TxStatus
	}

}
