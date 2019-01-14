package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait TxStatusBindings[TxStatus] {
	self : SessionService[_, _, _, _, TxStatus, _, _] =>

	def TxStatus : TxStatusOps

	trait TxStatusOps {
		def ABORTED : TxStatus
		def COMMITTED : TxStatus
		def PENDING : TxStatus
	}
}
