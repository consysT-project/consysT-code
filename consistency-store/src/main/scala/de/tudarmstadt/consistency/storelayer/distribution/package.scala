package de.tudarmstadt.consistency.storelayer

/**
	* Created on 14.01.19.
	*
	* @author Mirko Köhler
	*/
package object distribution {


	case class OpRef[Id, Key](id : Id, key : Key) {
		require(id != null)
		require(key != null)

		def toTuple : (Id, Key) =	(id, key)
	}
	case class TxRef[Txid](txid : Txid) {
		require(txid != null)
	}



}
