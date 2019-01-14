package de.tudarmstadt.consistency.storelayer.distribution

/**
	* Created on 07.01.19.
	*
	* @author Mirko Köhler
	*/
trait TxidService[Txid] {
	self : SessionService[_, Txid, _, _, _, _, _] =>

	def freshTxid() : Txid

}
